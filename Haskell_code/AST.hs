-- Copyright (c) 2012-2015 Rishiyur S. Nikhil.  All Rights Reserved.

-- Abstract syntax of kernel BSV programs

module AST
where

-- ================================================================
-- Synonyms for convenience

type Program  = ([Binding], Schedule)

type Ide      = String      -- Identifiers
type RuleName = String      -- Rule names
type MethName = String      -- Method names
type HierName = [Ide]       -- [module instance, module instance, ..., {rule_name,method_name,moduleinstance_name}]

type Binding  = (Expr, Expr)
type Schedule = [HierName]  -- list of rule instances

-- ================================================================
-- Rules in modules

data Rule = Rule Ide Expr    -- Rule rulename (When condExpr bodyExpr)
    deriving (Show)

-- ================================================================
-- Method definitions

data MethDef = MethDef { methKind :: String    -- "V" (value), "A" (action) or "AV" (actionvalue)
                       , methName :: Ide
                       , methBody :: Expr      -- When methcond (Lambda [arg..arg] (Block [stmt..stmt]))
                       }
    deriving (Show)

-- ================================================================
-- Expression Grammar
--     expr  ::= var | const | ( expr ) | unop expr | expr binop expr
--     var   ::= letter { letter | digit }*
--     const ::= true | false
--     unop  ::= !
--     binop  ::= + | - | * | / | << | >> | == | != | < | <= | > | >= | && | || | .

data Expr = EIde String             -- Identifier

          | Void                    -- Constant void
          | ConstI Int              -- Constant integer
          | ConstS String           -- Constant string
          | PrimFn Opcode           -- Constant primitive function value
          | Lambda [Expr] Expr      -- args have form 'EIde x'
          | App [Expr]              -- apply e0 to e1, e2, ...
          | If Expr Expr Expr       -- Conditional
          | While Expr Expr         -- Loop

          | MethodVal Expr MethName -- Method value: Expr evaluates to a module instance

          | Block [Stmt]            -- Block

          | When Expr Expr          -- When guard-cond value

          | ModuleExpr [Binding] [Rule] [MethDef]

          -- The following only appear during static elaboration
          | ModuleInstRef Int   -- index into global IntMap of module instances

          -- The following only appear during dynamic execution
          | Unavail             -- due to a method condition being False
          | Closure Env Expr    -- value of a lambda
    deriving (Show)

instance Eq (Expr) where
    (EIde s1)                  == (EIde s2)               = (s1 == s2)
    (ConstI j1)                == (ConstI j2)             = (j1 == j2)
    (ConstS s1)                == (ConstS s2)             = (s1 == s2)
    (PrimFn op1)               == (PrimFn op2)            = (op1 == op2)
    (MethodVal mir1 methName1) == (MethodVal mir2 methName2) = (mir1 == mir2) && (methName1 == methName2)
    (ModuleInstRef mir1)       == (ModuleInstRef mir2)    = (mir1 == mir2)
    Unavail                    == Unavail                 = True
    _                          == _                       = False

-- Opcodes of PrimFns

data Opcode = Not
            | Plus | Minus | Times | Divide
            | SHL | SHR
            | Eq | Neq | Lt | Leq | Gt | Geq
            | And | Or

            | PrimMkReg
            | PrimMkCReg
            | PrimDisplay
    deriving (Eq, Show)

data Stmt = StmtExpr Expr
          | StmtBinding Binding
    deriving (Show)

-- ================================================================
-- toConstI is a convenience used during execution that converts a Haskell Bool into an Expr

toConstI :: Bool -> Expr
toConstI True  = ConstI 1
toConstI False = ConstI 0

-- ================================================================
-- Enviroments: maps from identifiers to expressions

type EnvItem = (Expr,Expr)    -- (identifier, value)
type Env     = [EnvItem]

lookupEnv :: Ide -> Env -> Expr
lookupEnv s1 []                             = error ("lookupEnv: no such ide: " ++ s1)
lookupEnv s1 ((EIde s2, e):bs) | s1 == s2   = e
                               | otherwise  = lookupEnv s1 bs

-- ================================================================
-- Expr printers

putCommaSepExprs :: [Expr] -> IO ()
putCommaSepExprs [] = return ()
putCommaSepExprs [e] = printExpr "" e
putCommaSepExprs (e:es) = do { printExpr "" e; putStr ","; putCommaSepExprs es }

-- ----------------

printExpr :: String -> Expr -> IO ()
printExpr prefix (EIde s) = putStr s
printExpr prefix (ConstI j) = putStr (show j)
printExpr prefix (ConstS s) = putStr ("\"" ++ s ++ "\"")
printExpr prefix (PrimFn op) = putStr (show op)
printExpr prefix (MethodVal e methName) = do { printExpr "" e; putStr "."; putStr methName }
printExpr prefix (Lambda args body) =
    do putStr "(lambda ("; putCommaSepExprs args; putStr ") "; printExpr (prefix ++ "  ") body; putStr ")"
printExpr prefix (App (e:es)) = do { printExpr "" e; putStr "("; putCommaSepExprs es; putStr ")" }
printExpr prefix (Block stmts) = do { putStrLn ""; putStr prefix; putStrLn "begin"
                                    ; mapM_ (printStmt (prefix ++ "  ")) stmts
                                    ; putStr prefix; putStr "end"
                                    }
printExpr prefix (ModuleExpr bindings rules methods) =
    do putStrLn ""; putStr prefix; putStrLn "MODULE";
       mapM (printBinding (prefix ++ "    ")) bindings
       putStr prefix; putStrLn "  RULES"
       mapM (printRule (prefix ++ "    ")) rules
       putStr prefix; putStrLn "  METHODS"
       mapM (printMethDef (prefix ++ "    ")) methods
       putStr prefix; putStr "ENDMODULE"
printExpr prefix e = do putStr (show e)

-- ----------------

printBinding :: String -> Binding -> IO ()
printBinding prefix (EIde s, rhs) =
    do putStr prefix; putStr "let "; putStr s; putStr " = "
       printExpr (prefix ++ "  ") rhs; putStrLn ""

-- ----------------

printMethDef :: String -> MethDef -> IO ()
printMethDef prefix (MethDef methKind ide (When cond body)) =
    do putStr prefix; putStr "method "; putStr methKind; putStr " "; putStr ide;
       putStr " when ("; printExpr "" cond; putStrLn ");"
       putStr (prefix ++ "  "); printExpr (prefix ++ "  ") body; putStrLn ""
       putStr prefix; putStrLn "endmethod"

-- ----------------

printStmt :: String -> Stmt -> IO ()
printStmt prefix (StmtExpr e)     = do putStr prefix; printExpr prefix e; putStrLn ";"
printStmt prefix (StmtBinding b)  = do printBinding prefix b

-- ----------------

printRule :: String -> Rule -> IO ()
printRule prefix (Rule name (When eCond eBody)) =
    do putStr prefix; putStr "rule "; putStr name; putStr " when ("; printExpr "" eCond; putStr ");"
       printExpr (prefix ++ "  ")  eBody; putStrLn ""

-- ================

printEnvItem :: String -> EnvItem -> IO ()
printEnvItem prefix (EIde s, e) =
    do putStr prefix; putStr s; putStr " = "
       printExpr (prefix ++ "  ") e; putStrLn ""

-- ================================================================
