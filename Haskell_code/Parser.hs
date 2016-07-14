-- Copyright (c) 2012-2015 Rishiyur S. Nikhil.  All Rights Reserved.

-- Parser from text concrete syntax to AST data structures for kernel BSV programs.
-- Uses the standard 'Parsec' Haskell library to specify a parser from
-- concrete syntax into ASTs.

module Parser
where

import qualified Control.Applicative  as CA ( (<*) )
import qualified Text.ParserCombinators.Parsec          as TP
-- import qualified Text.ParserCombinators.Parsec.String   as TPS
import qualified Text.ParserCombinators.Parsec.Prim     as TPPP
import qualified Text.ParserCombinators.Parsec.Expr     as TPE
import qualified Text.ParserCombinators.Parsec.Token    as TPT
import qualified Text.ParserCombinators.Parsec.Language as TPL

import AST

-- ================================================================
-- Top-level parser
-- Returns list of bindings and a schedule (list of hierarchical rulenames)

parseProgramFromString :: String -> Program
parseProgramFromString s = case (TP.parse programParser "" s) of
                               Left err -> error ("Error parsing input:" ++ show err)
                               Right ans -> ans

programParser :: TPPP.Parser Program
programParser = m_whiteSpace >> do bindings <- TP.many moduleParser  CA.<*  m_symbol "schedule"
                                   schedule <- TP.many hierRuleNameParser  CA.<*  TP.eof
                                   return (bindings, schedule)

-- ================================================================
-- Modules

moduleParser :: TPPP.Parser Binding
moduleParser = do m_reserved "module"
                  ide <- m_identifier
                  params <- do { m_symbol "#"; m_parens (m_commaSep m_identifier) } TP.<|> return []
                  m_symbol ";"
                  bindings <- TP.many modBindingParser  CA.<*  m_reserved "rules"
                  rules    <- TP.many ruleParser  CA.<*  m_reserved "methods"
                  methods  <- TP.many methDefParser  CA.<*  m_reserved "endmodule"
                  return $ (EIde ide, Lambda (map EIde params) (ModuleExpr bindings rules methods))

modBindingParser :: TPPP.Parser Binding
modBindingParser = do b <- bindingParser; m_symbol ";"; return b

-- ================================================================
-- Bindings

bindingParser :: TPPP.Parser Binding
bindingParser =
    do { m_reserved "let"; v <- m_identifier; m_symbol "="; e <- exprParser;
       ; return (EIde v, e) }

-- ================================================================
-- Rules (inside a ModuleExpr)

ruleParser :: TPPP.Parser Rule
ruleParser = do m_reserved "rule"; ide <- m_identifier; e <- (m_parens exprParser TP.<|> return (ConstI 1)); m_symbol ";"
                ss <- stmtSeqParser "endrule"
                return $ Rule ide (When e (Block ss))

-- ================================================================
-- Method definitions (inside a ModuleExpr)

methDefParser :: TPPP.Parser MethDef
methDefParser = do m_reserved "method"
                   methkind <- m_identifier    -- "V", "A" or "AV"
                   ide <- m_identifier
                   args <- (m_parens (m_commaSep m_identifier) TP.<|> return [])
                   methCond <- do { m_reserved "if"; m_parens exprParser } TP.<|> return (ConstI 1)
                   m_symbol ";"
                   ss <- stmtSeqParser "endmethod"
                   return $ MethDef methkind ide (When methCond (Lambda (map EIde args) (Block ss)))

-- ================================================================
-- Expressions

exprParser :: TPPP.Parser Expr
exprParser = TPE.buildExpressionParser  operator_table  term  TP.<?>  "expression"

-- Applications: t (arg1, ..., argN)
term :: TPPP.Parser Expr
term = do { t <- term1
          ; TP.try (arglist t) TP.<|> return t
          }

-- Methods: t.methodname
term1 :: TPPP.Parser Expr
term1 = do { t <- term2
           ; TP.try (do { m_symbol "."; m <- m_identifier; return $ MethodVal t m}) TP.<|> return t
           }

-- General expressions
term2 :: TPPP.Parser Expr
term2 = -- (e)
        m_parens exprParser
        -- Void
        TP.<|> do { m_symbol "("; m_symbol ")"; return Void }
        -- Ide
        TP.<|> fmap EIde m_identifier
        -- integer literals
        TP.<|> (m_integer >>= (\j -> return (ConstI $ fromInteger j)))
        -- string literals
        TP.<|> (m_string >>= (\s -> return (ConstS s)))
        -- True (bool literal)
        TP.<|> (m_reserved "True" >> return (ConstI 1))
        -- False (bool literal)
        TP.<|> (m_reserved "False" >> return (ConstI 0))
        -- if (b) t else e
        TP.<|> do m_reserved "if"
                  b <- m_parens exprParser
                  t <- exprParser
                  m_reserved "else"
                  e <- exprParser
                  return (If b t e)
        -- while (b) e
        TP.<|> do m_reserved "while"
                  b <- m_parens exprParser
                  e <- exprParser
                  return (While b e)
        -- begin s1 ... sN end
        TP.<|> do m_reserved "begin"
                  ss <- stmtSeqParser "end"
                  return (Block ss)

-- Table of prefix and infix operators

operator_table =
          [ [TPE.Prefix (m_reservedOp "!" >> return (unopApp (PrimFn Not)))]

          , [TPE.Infix (m_reservedOp "/" >> return (binopApp (PrimFn Divide))) TPE.AssocLeft]
          , [TPE.Infix (m_reservedOp "*" >> return (binopApp (PrimFn Times))) TPE.AssocLeft]
          , [TPE.Infix (m_reservedOp "-" >> return (binopApp (PrimFn Minus))) TPE.AssocLeft]
          , [TPE.Infix (m_reservedOp "+" >> return (binopApp (PrimFn Plus))) TPE.AssocLeft]

          , [TPE.Infix (m_reservedOp ">>" >> return (binopApp (PrimFn SHR))) TPE.AssocLeft]
          , [TPE.Infix (m_reservedOp "<<" >> return (binopApp (PrimFn SHL))) TPE.AssocLeft]

          , [TPE.Infix (m_reservedOp "==" >> return (binopApp (PrimFn Eq))) TPE.AssocLeft]
          , [TPE.Infix (m_reservedOp "!=" >> return (binopApp (PrimFn Neq))) TPE.AssocLeft]
          , [TPE.Infix (m_reservedOp "<" >> return (binopApp (PrimFn Lt))) TPE.AssocLeft]
          , [TPE.Infix (m_reservedOp "<=" >> return (binopApp (PrimFn Leq))) TPE.AssocLeft]
          , [TPE.Infix (m_reservedOp ">=" >> return (binopApp (PrimFn Geq))) TPE.AssocLeft]
          , [TPE.Infix (m_reservedOp ">" >> return (binopApp (PrimFn Gt))) TPE.AssocLeft]

          , [TPE.Infix (m_reservedOp "&&" >> return (binopApp (PrimFn And))) TPE.AssocLeft]
          , [TPE.Infix (m_reservedOp "||" >> return (binopApp (PrimFn Or))) TPE.AssocLeft]
          ]

unopApp :: Expr -> Expr -> Expr
unopApp op arg = App [op, arg]

binopApp :: Expr -> Expr -> Expr -> Expr
binopApp op arg1 arg2 = App [op, arg1, arg2]

-- Applications: e is a function; parses the arg list in parens and returns the application
arglist :: Expr -> TPPP.Parser Expr
arglist e = do { es <- m_parens (m_commaSep exprParser)
               ; return (App (e:es))
               }

-- ================================================================
-- Action statements

stmtSeqParser :: String -> TPPP.Parser [Stmt]
stmtSeqParser terminator = m_semiSep (stmtParser terminator)  CA.<*  m_reserved terminator

stmtParser :: String -> TPPP.Parser Stmt
stmtParser terminator=
    do { b <- bindingParser; return $ StmtBinding b }
    TP.<|> do { e <- exprParser; return $ StmtExpr e }

-- ================================================================
-- Hierarchical Rule Names (part of rule schedule)

hierRuleNameParser :: TPPP.Parser HierName
hierRuleNameParser = do m_symbol "["
                        xs <- m_commaSep m_identifier
                        m_symbol "]"
                        return xs

-- ================================================================
-- Lexical Tokens

-- Define the lexical structure
lexdef = TPL.emptyDef{ TPT.commentStart = "/*"
                     , TPT.commentEnd = "*/"
                     , TPT.commentLine = "--"
                     , TPT.identStart = TP.letter TP.<|> TP.char '_' TP.<|> TP.char '$'
                     , TPT.identLetter = TP.alphaNum TP.<|> TP.char '_'
                     , TPT.opStart = TP.oneOf "!&|=+-*/:<>"
                     , TPT.opLetter = TP.oneOf "&|=:<>"
                     , TPT.reservedOpNames = ["!", "&&", "||"
                                             , "==", "!=", "<", "<=", ">=", ">"
                                             , "+", "-", "*", "/"
                                             , "=", ">>", "<<"]
                     , TPT.reservedNames = [ "rules", "methods"
                                           , "True", "False"
                                           , "let"
                                           , "if", "else"
                                           , "rule", "endrule", "module", "endmodule", "method", "endmethod"
                                           , "while", "begin", "end"
                                           , "schedule"]
                     }

-- Create token parsers
TPT.TokenParser{ TPT.parens = m_parens
               , TPT.identifier = m_identifier
               , TPT.integer = m_integer
               , TPT.stringLiteral = m_string
               , TPT.reservedOp = m_reservedOp
               , TPT.reserved = m_reserved
               , TPT.semiSep = m_semiSep
               , TPT.commaSep = m_commaSep
               , TPT.symbol = m_symbol
               , TPT.whiteSpace = m_whiteSpace } = TPT.makeTokenParser  lexdef

-- ****************************************************************
-- Test parser

testParser :: String -> IO ()
testParser filename = do putStrLn "Parsing from stdin ..."
                         text <- readFile filename
                         let (bindings, schedule) = parseProgramFromString text
                         putStrLn "top-level bindings"
                         mapM (printBinding "  ") bindings
                         putStrLn "schedule"
                         mapM (\hn -> do { putStr "  "; print hn}) schedule
                         return ()

-- ================================================================
