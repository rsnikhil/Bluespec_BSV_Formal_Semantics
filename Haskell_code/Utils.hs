-- Copyright (c) 2012-2015 Rishiyur S. Nikhil.  All Rights Reserved.

module Utils
where

prindent :: Show t => String -> t -> IO ()
prindent indent x = do putStr indent; print x

lookup1 :: (Eq a,Show a) => a -> [(a,b)] -> b
lookup1 x xys = case lookup x xys of
                    Nothing -> error ("lookup1: cannot find key " ++ show x)
                    Just y  -> y

debugLevel :: Int
debugLevel = 1

debugPrint :: Int -> IO () -> IO ()
debugPrint n io | n <= debugLevel = io
                | otherwise       = return ()
