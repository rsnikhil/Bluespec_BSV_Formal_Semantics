-- Copyright (c) 2012-2015 Rishiyur S. Nikhil.  All Rights Reserved.

-- Syntax and semantics of kernel BSV programs.

import System.Environment

import Utils
import AST
import Parser
import StaticElab
import Semantics

main :: IO ()
main = do
          progName <- getProgName
          args <- getArgs

          if (length args /= 2) then
              do putStr  "Usage: "
                 putStr  progName
                 putStrLn  "  cycle-limit  input-file"

          else
              do
                 let [cycleLimit_String, filename] = args
                 let cycleLimit = read  cycleLimit_String

                 -- Read the input file
                 debugPrint 1 (do { putStr "---- Input file  "; putStrLn filename })
                 text <- readFile filename

                 -- Parse
                 let (bindings, schedule) = parseProgramFromString text
                 debugPrint 1 (do { putStrLn "---- Top-level bindings"
                                  ; mapM (printBinding "  ") bindings

                                  ; putStrLn "---- Schedule"
                                  ; mapM_ (\hn -> do { putStr "  "; print hn}) schedule})

                 -- Static elaboration
                 let (system, main_v) = staticElab bindings
                 debugPrint 1 (do { putStrLn "---- Elaborated program"
                                  ; printSystem True system
                                  ; putStr "value of main(): " ; print main_v})

                 -- Execute
                 system' <- exec_n_clocks system schedule cycleLimit
                 debugPrint 1 (do { putStrLn "---- final system: ";
                                  ; printSystem False system'})
