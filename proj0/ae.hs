{-# LANGUAGE GADTs #-}

-- Imports for QuickCheck
import System.Random
import Test.QuickCheck
import Test.QuickCheck.Gen
import Test.QuickCheck.Function
import Test.QuickCheck.Monadic

-- Imports for Parsec
import Control.Monad
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Token

-- Imports for PLIH
import ParserUtils

--
-- Simple caculator over naturals with no identifiers
--
-- Author: Perry Alexander
-- Date: Mon Jun 27 13:34:57 CDT 2016
--
-- Source files for the Arithmetic Expressions (AE) language from PLIH
--

-- AST Definition

data AE where
  Num :: Int -> AE
  Plus :: AE -> AE -> AE
  Minus :: AE -> AE -> AE
  Mult :: AE -> AE -> AE
  Div :: AE -> AE -> AE
  -- Has to be capital (unfortunately) as a constructor
  If0 :: AE -> AE -> AE -> AE
  deriving (Show,Eq)

-- AST Pretty Printer

-- NOTE: Added multiplication and division
pprint :: AE -> String
pprint (Num n) = show n
pprint (Plus n m) = "(" ++ pprint n ++ "+" ++ pprint m ++ ")"
pprint (Minus n m) = "(" ++ pprint n ++ "-" ++ pprint m ++ ")"

pprint (Mult n m) = "(" ++ pprint n ++ "*" ++ pprint m ++ ")"
pprint (Div n m) = "(" ++ pprint n ++ "/" ++ pprint m ++ ")"

pprint (If0 m n o) = "(if " ++ pprint m ++ " then " ++ pprint n ++ " else " ++ pprint m ++ ")"

--instance Show AE where
--  show = pprint

-- Parser (Requires ParserUtils and Parsec)

expr :: Parser AE
expr = buildExpressionParser operators term

-- NOTE: Added multiplication and division
operators = [ 
              [ inFix "*" Mult AssocLeft
              , inFix "/" Div AssocLeft ]
              ,
              [ inFix "+" Plus AssocLeft
              , inFix "-" Minus AssocLeft ]
            ]

numExpr :: Parser AE
numExpr = do i <- integer lexer
             return (Num (fromInteger i))

-- mostly from here:
-- https://wiki.haskell.org/Parsing_expressions_and_statements#Statement_parser
if0Expr :: Parser AE
if0Expr = do 
            reserved lexer "if0"
            n <- expr
            reserved lexer "then"
            m <- expr
            reserved lexer "else"
            o <- expr
            return (If0 n m o)

term = parens lexer expr <|> numExpr <|> if0Expr

-- Parser invocation

-- NOTE:
-- Accepts input like `parseAE "5+10/2"`, returns an Abstract form
-- (Didn't realize the quotes were necessary for a bit)
parseAE :: String -> AE

parseAE = parseString expr

parseAEFile = parseFile expr

-- Evaluation Function

-- NOTE:
-- Accepts input like `eval (Plus t1 t2)` exactly, returns AE result of
-- operation.
eval :: AE -> AE
eval (Num x) = (Num x)

eval (Plus t1 t2) = let (Num v1) = (eval t1)
                        (Num v2) = (eval t2)
                    in (Num (v1+v2))
eval (Minus t1 t2) = let (Num v1) = (eval t1)
                         (Num v2) = (eval t2)
                     in (Num (v1-v2))


eval (Mult t1 t2) = let (Num v1) = (eval t1)
                        (Num v2) = (eval t2)
                    in (Num (v1*v2))
eval (Div t1 t2) = let (Num v1) = (eval t1)
                       (Num v2) = (eval t2)
                   in (Num (div v1 v2))
eval (If0 t1 t2 t3) = let (Num v1) = (eval t1)
                          (Num v2) = (eval t2)
                          (Num v3) = (eval t3)
                      in case v1 of 0 -> (Num v2)
                                    _ -> (Num v3)

-- Interpreter = parse + eval

-- NOTE:
-- Accepts input like `interp "5+10/2"`, returns eval'd value.
interp :: String -> AE
interp = eval . parseAE

-- Testing (Requires QuickCheck 2)

-- Arbitrary AST Generator

instance Arbitrary AE where
  arbitrary =
    sized $ \n -> genAE ((rem n 10) + 10)

genNum =
  do t <- choose (0,100)
     return (Num t)

genPlus n =
  do s <- genAE n
     t <- genAE n
     return (Plus s t)

genMinus n =
  do s <- genAE n
     t <- genAE n
     return (Minus s t)

genAE :: Int -> Gen AE
genAE 0 =
  do term <- genNum
     return term
genAE n =
  do term <- oneof [genNum,(genPlus (n-1)),(genMinus (n-1))]
     return term

-- QuickCheck 

testParser :: Int -> IO ()
testParser n = quickCheckWith stdArgs {maxSuccess=n}
  (\t -> parseAE (pprint t) == t)

testEval' :: Int -> IO ()
testEval' n = quickCheckWith stdArgs {maxSuccess=n}
  (\t -> (interp $ pprint t) == (eval t))
