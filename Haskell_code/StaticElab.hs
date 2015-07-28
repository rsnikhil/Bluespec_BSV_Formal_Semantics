-- Copyright (c) 2012-2015 Rishiyur S. Nikhil.  All Rights Reserved.

-- Static elaboration of kernel BSV programs

module StaticElab
where

import Data.List
import qualified Data.IntMap as DI

import Utils
import AST
import Parser

-- ================================================================
-- A module instance value:
--     Instance of a primitive module (PMI)
--     Instance of a user-defined module (UMI) containing
--         an Environment (its bindings),
--         its Rules (free vars should be bound in the Env)
--         its Method Definitions (free vars should be bound in the Env)

data ModuleInst = PMIReg      Int               -- reg data
                | PMICReg Int Int               -- # of ports, reg data
                | UMI     Env [Rule] [MethDef]  -- User-defined module instance
    deriving (Show)

-- Primitive module types

data ModuleType = Reg
                | CReg
                | U    -- User defined module
    deriving (Show, Eq)

typeOfMI :: ModuleInst -> ModuleType
typeOfMI (PMIReg j)    = Reg
typeOfMI (PMICReg n x) = CReg
typeOfMI (UMI _ _ _)   = U

select_UMI_method :: String -> ModuleInst -> MethDef
select_UMI_method methname umi = case mds of
                                     [md]      -> md
                                     otherwise -> error errstring
    where
        (UMI _ _ methdefs) = umi
        mds = [ mdJ | mdJ <- methdefs, methName mdJ == methname ]
        errstring = "select_UMI_method: " ++ methname ++ " " ++ show umi

-- ================================================================
-- A ``system'' is a collection of module instances
-- Each instance is identified by a unique integer id (key of IntMap)
-- and contains its hierarchical name and a ModuleInst (value of IntMap)

type System = DI.IntMap (HierName, ModuleInst)

extendSystem :: System -> HierName -> ModuleInst -> (System, Expr)
extendSystem system hiername e = (system', ModuleInstRef n)
    where
        n = DI.size system
        system' = DI.insert n (hiername, e) system

-- ================================================================
-- Static Elaboration works on the top-level bindings of the source program
-- It evaluates the application 'main ()'
-- and returns a System the value of the application

staticElab :: [Binding] -> (System, Expr)
staticElab bindings = eval  []  ["main"]  DI.empty  (App [EIde "main"])
    where
        primitivesEnv :: Env
        primitivesEnv = [ (EIde "mkReg",  PrimFn PrimMkReg)
                        , (EIde "mkCReg", PrimFn PrimMkCReg)
                        ] 

        staticEnv :: Env
        staticEnv = primitivesEnv ++ bindings

        -- Eval
        eval :: Env -> HierName -> System -> Expr -> (System, Expr)
        eval env hn system (EIde s)      = (system, lookupEnv s (staticEnv ++ env))
        eval env hn system (ConstI j)    = (system, ConstI j)
        eval env hn system (ConstS s)    = (system, ConstS s)
        eval env hn system (PrimFn op)   = (system, PrimFn op)
        eval env hn system (Lambda xs e) = (system, Lambda xs e)
        eval env hn system (App es) = let
                                          -- Evaluate all the expressions in es
                                          (system', vF:vArgs) = mapAccumL (eval env hn) system es
                                      in
                                          -- Apply the function value to the arg values
                                          app hn system' vF vArgs
        eval env hn system (ModuleExpr bs rs mds) =
                        let
                            -- Convert the bindings into an environment,
                            -- sequentially evaluating the right-hand sides
                            f (system, env) (lhs @ (EIde s), rhs) = (system', env')
                                where
                                    (system', v) = eval env (hn ++ [s]) system rhs
                                    env' = env ++ [(lhs, v)]
                            (system', env') = foldl f (system, []) bs

                            -- Create a user-defined module instance
                            new_umi = UMI (env ++ env') rs mds
                        in
                            extendSystem system' hn new_umi

        -- Apply
        app :: HierName -> System -> Expr -> [Expr] -> (System, Expr)
        app hn system (PrimFn PrimMkReg) [ConstI j] = extendSystem system hn (PMIReg j)
        app hn system (PrimFn PrimMkCReg) [ConstI n, ConstI j] = extendSystem system hn (PMICReg n j)

        app hn system (PrimFn Plus) [ConstI a, ConstI b] = (system, ConstI (a+b))
        app hn system (PrimFn Minus) [ConstI a, ConstI b] = (system, ConstI (a-b))
        app hn system (PrimFn Times) [ConstI a, ConstI b] = (system, ConstI (a*b))
        app hn system (PrimFn Divide) [ConstI a, ConstI b] = (system, ConstI (div a b))

        app hn system (Lambda xs e) ys = eval (zip xs ys) hn system e
        app hn system f args = error ("staticElab.app: not implemented: " ++ show (f:args))

-- ****************************************************************
-- Printing

printSystem :: Bool -> System -> IO ()
printSystem showUMIs system =
    do
       let jvs = DI.toAscList system
       mapM (\(j, (hn, mi)) -> do { putStr "  "
                                  ; putStr (show j); putStr " "
                                  ; putStr (show hn)
                                  ; printModuleInst showUMIs "    " mi
                                  })
            jvs
       return ()

-- ----------------

printModuleInst :: Bool -> String -> ModuleInst -> IO ()
printModuleInst True prefix (UMI env rules methDefs) =
    do putStrLn ""; putStr prefix; putStrLn "UMI ";
       mapM (printEnvItem (prefix ++ "    ")) env
       putStr prefix; putStrLn "  RULES"
       mapM (printRule (prefix ++ "    ")) rules
       putStr prefix; putStrLn "  METHODS"
       mapM (printMethDef (prefix ++ "    ")) methDefs
       putStr prefix; putStrLn "EUMI"
printModuleInst False prefix (UMI env rules methDefs) =
    do putStrLn "UMI ...";
printModuleInst _     prefix mi = do putStr prefix; putStrLn (show mi)

-- ****************************************************************
-- Testing

testStaticElab :: String -> IO ()
testStaticElab filename =
    do putStr "---- Parsing  "; putStrLn filename;
       c <- readFile filename
       let (bindings, hiernames) = parseProgramFromString c

       putStrLn "---- Top-level bindings"
       mapM (printBinding "  ") bindings

       putStrLn "---- Schedule"
       mapM (\hn -> do { putStr "  "; print hn}) hiernames

       putStrLn "---- Elaborated program"
       let (system,v) = staticElab bindings
       printSystem True system
       putStr "value of main(): " ; print v

-- ================================================================
