-- Copyright (c) 2012-2015 Rishiyur S. Nikhil.  All Rights Reserved.

-- Dynamic semantics of kernel BSV programs

module Semantics
where

import Control.Monad    -- for foldM
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap

import Utils
import AST
import StaticElab

-- ================================================================
-- Exec for nclocks, or until no rule fires in a clock
-- If nclocks is -1, it is interpreted as 'infinity', i.e., unlimited number of clocks

exec_n_clocks :: System -> Schedule -> Int -> IO System
exec_n_clocks  system  schedule  nclocks = loop  system  0
    where
        -- Convert the schedule in to a sequence (list) of corresponding rules
        ruleSeq :: [(HierName, Env, Rule)]
        ruleSeq = map  (findRule  system)  schedule

        -- Exec for n = 0 .. (n clocks -1 )
        loop system j = do putStr ".... Clock "; print j

                           -- Exec for 1 clock
                           (anyfired, system') <- exec_1_clock system ruleSeq

                           -- Loop, or stop if no rules fired or nclocks done
                           if (not anyfired) then
                               do putStrLn $ "No rule fired on cycle " ++ show (j); return system'
                           else if (nclocks >= 0) && (j >= nclocks) then
                               do putStrLn $ "Cycle limit reached: " ++ show (j); return system'
                           else
                               loop system' (j+1)

-- ----------------
-- Retrieve a rule from the system, given its hierarchical name
-- hierRuleName is [ modInstName, ..., modInstName, ruleName]
-- The retrieved Env binds any free variables in the retrieved Rule (i.e., this is a closure)

findRule :: System -> HierName -> (HierName, Env, Rule)
findRule system hierRuleName = (hierRuleName, initEnv ++ env, rule)
    where
        modInstNames  = init hierRuleName    -- all but last
        ruleName      = last hierRuleName
        [(env, rule)] = [ (env', rule')
                         | (j, (modInstNames', UMI env' rules' methDefs')) <- IntMap.toList system
                         , modInstNames' == modInstNames
                         , rule' <- rules'
                         , let Rule ruleName' e' = rule'
                         , ruleName == ruleName' ]

-- ----------------
-- Initial environment, binding the 'display' function

initEnv = [(EIde "$display", PrimFn PrimDisplay)]

-- ================================================================
-- Exec a rule sequence in a system for one clock
-- returning the updated system
-- and a bool indicating whether any rules fired

exec_1_clock :: System -> [(HierName,Env,Rule)] -> IO (Bool, System)
exec_1_clock system ruleSeq = do (anyfired, system', _) <- foldM f  (False, system, [])  ruleSeq
                                 return (anyfired, system')
    where
        -- mcsPrev is the collection of methods-called in rules previously fired in this clock
        f (anyfired, system, mcsPrev) rule =
            do (fired, system', mcsPrev') <- execRule system mcsPrev rule
               return (anyfired || fired, system', mcsPrev')

-- ================================================================
-- Exec a rule in a system
-- This is the central and most important function of these semantics.
-- A rule is given by its (hierarchical name, environment for free vars, rule expression)
-- mcsPrev is the collection of methods-called in rules that fired previously in this clock
-- Returns a bool (whether this rule fired or not),
--         the updated system
--         an updated list of methods-called (same as incoming list of methods-called if rule doesn't fire)

-- Methods called
type MC = Expr    -- MethodVal (ModuleInstRef j) MethName

execRule :: System -> [MC] -> (HierName, Env, Rule) -> IO (Bool, System, [MC])  -- Bool is 'rule fired'
execRule  system  mcsPrev  (hname, env, Rule name e) =
    do debugPrint 2 (putStrLn ("execRule " ++ show hname))

       -- Eval this rule, returning its value, its actions and its methods-called
       (v,actions,mcsThis) <- evalExpr system env e
       debugPrint 2 (putStrLn ("execRule: mcsThis = " ++ show (mcsThis)))

       let intra_cfs = intraRuleConflicts  system  mcsThis
       let inter_cfs = interRuleConflicts  system  mcsPrev  mcsThis
       let hw_cfs    = hwConflicts         system  mcsPrev  mcsThis

       if not (intra_cfs == []) then
            -- has intra-rule method conflicts
            do debugPrint 1 (do { putStrLn $ "  Rule " ++ show hname
                                ; putStrLn "    intra-rule conflicts:"
                                ; mapM_ (printConflict system "     ") intra_cfs })
               return (False, system, mcsPrev)

       else if not (inter_cfs == []) then
            -- has inter-rule method conflicts
            do debugPrint 1 (do { putStrLn $ "  Rule " ++ show hname
                                ; putStrLn "    inter-rule conflicts:"
                                ; mapM_ (printConflict system "      ") inter_cfs })
               return (False, system, mcsPrev)

       else if not (hw_cfs == []) then
            -- has hardware method conflicts
            do debugPrint 1 (do { putStrLn $ "  Rule " ++ show hname
                                ; putStrLn "    hardware conflicts:"
                                ; mapM_ (printConflict system "      ") hw_cfs })
               return (False, system, mcsPrev)

       else if (v == Unavail) then
            -- Rule is not enabled (rule cond, or some method cond, is false)
            do debugPrint 1 (do { putStr $ "  Rule " ++ show hname; putStrLn " unavail"})
               return (False, system, mcsPrev ++ mcsThis)

       else
            -- Rule is enabled (rule-cond is True and all method-conds are True)
            -- Perform the rule's actions, updating the system state
            do debugPrint 1 (do { putStr $ "  Rule " ++ show hname; putStrLn " fired"})
               debugPrint 2 (do { putStrLn "  Performing Actions "
                                ; mapM (prindent "    ") actions; return () })
               system' <- doActions system actions
               debugPrint 2 (do { putStrLn "  Updated system:"; printSystem False system' })
               return (True, system', mcsPrev ++ mcsThis)

-- ****************************************************************
-- evalExpr: Evaluating expressions
-- Initially called from 'execRule', with a Rule as argument e,
--     and it recursively evaluates sub-expressions.
-- It is a kind of "dry-run" of rule execution in that it does not perform any Actions in the rule,
--     it just collects the Actions and returns them.
-- It also returns the Bool value of the method condition (True, False or Unavail)
--     and a list of all the methods-called.
--     Note that the Bool method condition value can never depend on an Action
--     (BSV type-checking ensures that).
-- 'execRule' will check the methods-called for various kinds of conflicts,
--     and whether the method condition is True,
--     and will only then perform the Actions that were collected by evalExpr.

-- Returns a triple of type (Value, [Action], [MC])
-- Values
type Val    = Expr    -- Unavail
                      -- Void, ConstI j, ConstS s,
                      -- PrimFn op,
                      -- Closure env (Lambda ...),
                      -- MethodVal (MmoduleInstRef j) MethName
-- Actions
type Action = Expr    -- App [MethodVal (ModuleInstRef j) MethName, Val_arg, ..., Val_arg]

evalExpr :: System -> Env -> Expr -> IO (Val, [Action], [MC])
evalExpr system env e =
    do debugPrint 3 (do { putStrLn "--> evalExpr"; putStr "    "; printExpr "    " e; putStrLn "" })

       (v,as,mcs) <- eval e

       debugPrint 3 (do { putStrLn "<-- evalExpr"
                        ; putStr " e=  "; printExpr "    " e; putStrLn ""
                        ; putStr " v=  "; printExpr "    " v; putStrLn ""
                        ; putStr " as= "; mapM (printExpr "    ") as; putStrLn ""
                        ; putStr " mcs="; print mcs; putStrLn "" })

       return (v,as,mcs)
    where
        eval :: Expr -> IO (Val, [Action], [MC])
        eval (EIde s)    = return (lookupEnv s env, [], [])
        eval (ConstI i)  = return (ConstI i, [], [])
        eval (ConstS s)  = return (ConstS s, [], [])
        eval (PrimFn op) = return (PrimFn op, [], [])
        eval (MethodVal e methName) = do (miref, [], mcs) <- evalExpr system env e
                                         return (MethodVal miref methName, [], mcs)
        eval (Lambda args body) = return (Closure env (Lambda args body), [], [])
        eval (App es)   =
            do (vs, as, mcs) <- evalList es
               if any (== Unavail) vs then
                   return (Unavail, as, mcs)
               else do (v, as', mcs') <- apply system vs
                       return (v, as++as', mcs++mcs')
        eval (If e0 e1 e2) = do (v0, as0, mcs0) <- eval e0
                                if (v0 == Unavail) then
                                    return (Unavail, as0, mcs0)
                                else if (v0 == (ConstI 1)) then
                                    do (v1, as1, mcs1) <- eval e1
                                       return (v1, as0++as1, mcs0++mcs1)
                                else
                                    do (v2, as2, mcs2) <- eval e2
                                       return (v2, as0++as2, mcs0++mcs2)
        eval (When econd ebody) = do (vcond, [], mcs) <- evalExpr system env econd
                                     if ((vcond == Unavail) || (vcond == (ConstI 0)))
                                     then return (Unavail, [], mcs)
                                     else do (vbody, as', mcs') <- evalExpr system env ebody
                                             if (vbody == Unavail) then return (Unavail, [], mcs)
                                             else return (vbody, as', mcs++mcs')
        eval (Block stmts) = evalStmts system env (Void, [], []) stmts

        -- Eval a list of expressions
        evalList :: [Expr] -> IO ([Val], [Action], [MC])
        evalList es = do xs <- mapM (evalExpr system env) es
                         let (vs, ass, mcss) = unzip3 xs
                         return (vs, concat ass, concat mcss)

-- ----------------
-- evalStmts: Eval a sequence of statements (typically Actions)

evalStmts :: System -> Env -> (Val, [Action], [MC]) -> [Stmt] -> IO (Val, [Action], [MC])
evalStmts system env (v, as, mcs)       []           = return (v, as, mcs)
evalStmts system env (Unavail, as, mcs) stmts        = return (Unavail, as, mcs)
evalStmts system env (v, as, mcs)       (stmt:stmts) =
  do
    case stmt of
        StmtExpr e         -> do (v', as', mcs') <- evalExpr system env e
                                 let as'' = as ++ as'
                                 let mcs'' = mcs ++ mcs'
                                 evalStmts system env (v', as'', mcs'') stmts
        StmtBinding (x, e) -> do (v', as', mcs') <- evalExpr system env e
                                 let env' = env ++ [(x, v')]
                                 let as'' = as ++ as'
                                 let mcs'' = mcs ++ mcs'
                                 evalStmts system env' (Void, as'', mcs'') stmts

-- ----------------
-- apply: Apply a function value to arg values

apply :: System -> [Expr] -> IO (Val, [Action], [MC])
apply system  (vf:vargs)  = do -- putStr "--> apply: "; printExpr "" vf; print vargs; putStrLn ""
                               (v, as, mcs) <- app vf vargs
                               -- putStr "<-- apply: "; printExpr "" vf; print vargs; putStrLn ""
                               -- putStr " v= "; printExpr " " v; putStrLn ""
                               return (v, as, mcs)
    where
        app       (PrimFn opcode)              vargs = do (y, as) <- applyPrimFn (PrimFn opcode) vargs
                                                          return (y, as, [])
        app       (Closure env (Lambda xs e))  vargs = evalExpr system (env ++ zip xs vargs) e
        app  mv @ (MethodVal miref methname)   vargs = applyMethod system mv vargs

-- ----------------
-- applyPrimFn: Apply primitive function value to arg values

applyPrimFn :: Val -> [Val] -> IO (Val, [Action])

-- Unary functions/ops
applyPrimFn (PrimFn Not)    [ConstI 0] = return (ConstI 1, [])
applyPrimFn (PrimFn Not)    [ConstI 1] = return (ConstI 0, [])

-- Binary functions/ops
applyPrimFn (PrimFn Plus)   [ConstI x, ConstI y] = return (ConstI (x+y), [])
applyPrimFn (PrimFn Minus)  [ConstI x, ConstI y] = return (ConstI (x-y), [])
applyPrimFn (PrimFn Times)  [ConstI x, ConstI y] = return (ConstI (x*y), [])
applyPrimFn (PrimFn Divide) [ConstI x, ConstI y] = return (ConstI (x `div` y), [])

applyPrimFn (PrimFn Eq)     [ConstI x, ConstI y] = return (toConstI (x == y), [])
applyPrimFn (PrimFn Neq)    [ConstI x, ConstI y] = return (toConstI (x /= y), [])
applyPrimFn (PrimFn Lt)     [ConstI x, ConstI y] = return (toConstI (x < y), [])
applyPrimFn (PrimFn Leq)    [ConstI x, ConstI y] = return (toConstI (x <= y), [])
applyPrimFn (PrimFn Gt)     [ConstI x, ConstI y] = return (toConstI (x > y), [])
applyPrimFn (PrimFn Geq)    [ConstI x, ConstI y] = return (toConstI (x >= y), [])

applyPrimFn (PrimFn And)    [ConstI x, ConstI y] = return (toConstI (x /= 0 && y /= 0), [])
applyPrimFn (PrimFn Or)     [ConstI x, ConstI y] = return (toConstI (x /= 0 || y /= 0), [])

-- Note: PrimDisplay (from $display) is an Action function, so don't do it, just collect it
applyPrimFn (PrimFn PrimDisplay) [ConstI x] = return (Void, [App [PrimFn PrimDisplay, ConstI x]])
applyPrimFn (PrimFn PrimDisplay) [ConstS s] = return (Void, [App [PrimFn PrimDisplay, ConstS s]])

applyPrimFn vop vargs = error ("applyPrimFn: not implemented " ++ show vop ++ "  " ++ show vargs)

-- ----------------
-- applyMethod: Apply a method value to arg values

applyMethod :: System -> Val -> [Val] -> IO (Val, [Action], [MC])
applyMethod system  mc@ (MethodVal  miref @ (ModuleInstRef j)  methname)  vargs =
    do let (hn, mi) = system IntMap.! j

       -- Record this method-called, whether it's a PMI or UMI
       let mcs = [mc]
       -- thisActions will only be used if this is not a Value method
       let thisActions = [App (mc:vargs)]

       case (mi, methname, vargs) of
           -- Methods of ordinary registers
           (PMIReg v, "_read", []) -> return (ConstI v, [], mcs)
           (PMIReg v, "_write", [v']) -> return (Void, thisActions, mcs)

           -- Methods of Concurrent registers
           (PMICReg n v, "_read0", [])                -> return (ConstI v, [], mcs)
           (PMICReg n v, "_write0", [v'])             -> return (Void, thisActions, mcs)

           (PMICReg n v, "_read1", [])    | n > 1     -> return (ConstI v, [], mcs)
                                          | otherwise -> error "applyMethod: CReg _read1: no such port"
           (PMICReg n v, "_write1", [v']) | n > 1     -> return (Void, thisActions, mcs)
                                          | otherwise -> error "applyMethod: CReg _write1: no such port"

           (PMICReg n v, "_read2", [])    | n > 2     -> return (ConstI v, [], mcs)
                                          | otherwise -> error "applyMethod: CReg _read2: no such port"
           (PMICReg n v, "_write2", [v']) | n > 2     -> return (Void, thisActions, mcs)
                                          | otherwise -> error "applyMethod: CReg _write2: no such port"

           -- Methods of User-defined modules
           (UMI env rules methDefs, _, _) ->
               do -- Select the method by name, getting its body and kind
                  let [(mbody, mkind)] = [ (mbody', mkind') | md <- methDefs
                                                            , let MethDef mkind' methname' mbody' = md
                                                            , methname == methname' ]
                  -- mbody is a lambda expr, evaluating to closure v
                  (v, actions, mcs') <- evalExpr system env mbody
                  -- let actions' = thisActions ++ actions
                  let actions' = if (mkind == "V") then [] else (thisActions ++ actions)
                  if (v == Unavail) then return (Unavail, actions', mcs++mcs')
                  else do (v', actions'', mcs'') <- apply system (v:vargs)
                          return (v', actions'++actions'', mcs++mcs'++mcs'')

           otherwise -> error $ concat ["appMeth: not implementend: modInst ", show j, " ", methname, "  ", show vargs]

-- ****************************************************************
-- Intra-rule conflicts (parallel composition)

-- Given a list of methods-called in a rule
-- Return all pairs of methods-called that have an intra-rule conflict

intraRuleConflicts :: System -> [MC] -> [(MC,MC)]
intraRuleConflicts system [] = []
intraRuleConflicts system (mc1:mcs) = [ (mc1,mc2) | mc2 <- mcs, intraRuleConflict system mc1 mc2]
                                      ++ intraRuleConflicts system mcs

-- Check if two methods-called have an intra-rule conflict:
--   - they are on the same module instance (j1 == j2), and
--   - the two methods are in the intra-rule conflict table

intraRuleConflict :: System -> MC -> MC -> Bool
intraRuleConflict  system  (MethodVal (ModuleInstRef j1) methName1)
                           (MethodVal (ModuleInstRef j2) methName2) | (j1 /= j2) = False    --different module instances
                                                                    | otherwise  = b
    where
        (hname, mi) = (system  IntMap.!  j1)
        pmtype = typeOfMI mi
        b = (   elem (pmtype, methName1, methName2) intraRuleConflictTable
             || elem (pmtype, methName2, methName1) intraRuleConflictTable)

-- Table of all intra-rule conflicts

intraRuleConflictTable :: [ (ModuleType, MethName, MethName) ]
intraRuleConflictTable =
    [ -- Reg ----------------
      -- _write cannot be called more than once in a rule
      (Reg, "_write", "_write")

      -- CReg ----------------
      -- _writes cannot be called more than once in a rule
    , (CReg, "_write0", "_write0"), (CReg, "_write0", "_write1"), (CReg, "_write0", "_write2")
    , (CReg, "_write1", "_write1"), (CReg, "_write1", "_write2")
    , (CReg, "_write2", "_write2")

      -- _write_0 cannot be called with _read_1 or _read2
    , (CReg, "_write0", "_read1"), (CReg, "_write0", "_read2")
      -- _write_1 cannot be called with _read_2
    , (CReg, "_write1", "_read2")
    ]

-- ----------------------------------------------------------------
-- Inter-rule conflicts (method order violations)

-- Given a list of methods-called in a rule (mcsThis)
-- and list of methods-called from rules fired previously in this clock (mcsPrev)
-- Return all pairs of methods-called that have an inter-rule (rule-order) conflict

interRuleConflicts :: System -> [MC] -> [MC] -> [(MC,MC)]
interRuleConflicts  system  mcsPrev  mcsThis = [ (mc1,mc2) | mc1 <- mcsPrev
                                                           , mc2 <- mcsThis
                                                           , interRuleConflict system mc1 mc2 ]

-- Given a method-called mc1 from a rule fired previously in this clock
-- and a method-called mc2 from the current rule
-- Check if the two methods-called have a rule-order conflict:
--   - they are on the same module instance (j1 == j2), and
--   - the two methods are in the inter-rule conflict table

interRuleConflict :: System -> MC -> MC -> Bool
interRuleConflict  system (MethodVal (ModuleInstRef j1) methName1)
                          (MethodVal (ModuleInstRef j2) methName2) | (j1 /= j2) = False
                                                                   | otherwise  = b
    where
        (hname, mi) = (system IntMap.! j1)
        pmtype = typeOfMI mi
        b = elem (pmtype, methName1, methName2) interRuleConflictTable

-- Table of all inter-rule conflicts

interRuleConflictTable :: [ (ModuleType, MethName, MethName) ]
interRuleConflictTable =
    [ -- Reg ----------------
      -- _write cannot precede _read
      (Reg, "_write", "_read")

      -- CReg ----------------
      -- _write2 cannot precede write_0, _write1, _read0, _read1, _read2,
    , (CReg, "_write2", "_write0"), (CReg, "_write2", "_write1")
      -- _write2 cannot precede _read0, _read1, _read2,
    , (CReg, "_write2", "_read0"),  (CReg, "_write2", "_read1"),  (CReg, "_write2", "_read2")

      -- _write1 cannot precede write_0
    , (CReg, "_write1", "_write0")
      -- _write1 cannot precede read0, read1
    , (CReg, "_write1", "_read0"),  (CReg, "_write1", "_read1")

      -- _write0 cannot precede read0
    , (CReg, "_write0", "_read0")
    ]

-- ----------------------------------------------------------------
-- Hardware conflicts

-- Given a list of methods-called
-- Return all pairs of methods-called that have a hardware conflict

hwConflicts :: System -> [MC] -> [MC] -> [(MC,MC)]
hwConflicts  system  mcsPrev  mcsThis = (hwConflictsThis system mcsThis) ++ (hwConflictsWithPrev system mcsPrev mcsThis)

-- In list of methods-called, check hardware conflict of each against all others
-- (i.e., excluding self)
hwConflictsThis system [] = []
hwConflictsThis system (mc1:mcs) = [ (mc1,mc2) | mc2 <- mcs, hwConflict system mc1 mc2]
                                   ++ (hwConflictsThis system mcs)

-- Check hardware conflict of each method-called in mcsThis against each method-called in mcsPrev
hwConflictsWithPrev system mcsPrev mcsThis = [ (mc1,mc2) | mc1 <- mcsPrev
                                                         , mc2 <- mcsThis
                                                         , hwConflict system mc1 mc2 ]

-- Check if two methods-called have a hardware conflict:
--   - they are for the same method on the same module instance
--   - and the method is an Action, ActionValue or non-niladic Value method
--      (in each of these cases, the hardware module has at least one input wire,
--       and input wires can only be driven once in each clock)

hwConflict :: System -> MC -> MC -> Bool
hwConflict system  (MethodVal (ModuleInstRef j)  methname)
                   (MethodVal (ModuleInstRef j2) methname2) | j /= j2               = False  -- different module instances
                                                            | methname /= methname2 = False  -- different methods
                                                            | otherwise             = b
    where
        (hname, mi) = (system IntMap.! j)
        b = case mi of
                -- Method on primitive module
                (PMIReg _)    -> (methname == "_write")
                (PMICReg _ _) -> (methname == "_write0") || (methname == "_write1") || (methname == "_write2")

                -- Method on user-defined module
                (UMI _ _ _)   -> let
                                     md                   = select_UMI_method  methname  mi
                                     Lambda args body     = methBody md
                                     niladic_Value_method = (   (methKind md == "V")
                                                             && (length args == 0))
                                 in
                                     not niladic_Value_method

-- ----------------------------------------------------------------
-- printConflict: for tracing and debugging

printConflict :: System -> String -> (MC,MC) -> IO ()
printConflict system prefix ((MethodVal (ModuleInstRef j1) methname1),
                             (MethodVal (ModuleInstRef j2) methname2)) =
    do putStr prefix; putStr (show hname1); putStr " "; putStr methname1; putStr " > "; putStrLn methname2
    where
        (hname1, _) = system IntMap.! j1

-- ****************************************************************
-- Performing actions
-- All side-effects of the rule happen here, instantaneous/simultaneous/parallel

-- ----------------
-- doActions: Perform the actions from a rule, updating the system.
-- This is called after it has been decided to commit a rule
-- (after checking all conflicts and rule/method conditions)

doActions :: System -> [Expr] -> IO System
doActions  system  actions = foldM  f  system  actions
    where
        f system (App (MethodVal (ModuleInstRef j) methName:args)) = return $ doAction system j methName args
        f system (App [PrimFn PrimDisplay, ConstI x]) = do { putStr "$DISPLAY: "; putStrLn (show x)
                                                           ; return system }
        f system (App [PrimFn PrimDisplay, ConstS s]) = do { putStr "$DISPLAY: "; putStrLn s
                                                           ; return system }

-- Perform a single action from a rule, updating the system

doAction :: System -> Int -> MethName -> [Val] -> System
doAction  system  j  methName  args = system'
    where
        -- Get the primitive module instance from the system
        (hname, mi) = system IntMap.! j
        -- Upate the primitive module instance according to the method
        mi' = case (mi, methName, args) of
                  (PMIReg v,    "_write",  [ConstI v']) -> PMIReg v'
                  (PMICReg n v, "_write0", [ConstI v']) -> PMICReg n v'
                  (PMICReg n v, "_write1", [ConstI v']) -> PMICReg n v'
                  (PMICReg n v, "_write2", [ConstI v']) -> PMICReg n v'
                  (UMI _ _ _, _, _) -> mi
                  otherwise -> error (concat [ "doAction: not implementend: modInst ", show j, " "
                                             , methName, "  ", show args])
        -- Put the new primitive module instance back in the system
        system' = IntMap.insert j (hname, mi') system

-- ================================================================
