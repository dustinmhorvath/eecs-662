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
-- Simple calculator language extended with no identifiers extended
-- with Booleans
--
-- Author: Perry Alexander
-- Date: Mon Jun 27 20:16:55 CDT 2016
--
-- Source files for the Arithmetic Boolean Expressions (ABE) language
-- from PLIH
--

-- AST Definition

data TABE where
  TNum :: TABE
  TBool :: TABE
  deriving (Show,Eq)

data ABE where
  Num :: Int -> ABE
  Mult :: ABE -> ABE -> ABE
  Div :: ABE -> ABE -> ABE
  Plus :: ABE -> ABE -> ABE
  Minus :: ABE -> ABE -> ABE
  Boolean :: Bool -> ABE
  And :: ABE -> ABE -> ABE
  Leq :: ABE -> ABE -> ABE
  IsZero :: ABE -> ABE
  If :: ABE -> ABE -> ABE -> ABE
  deriving (Show,Eq)

-- AST Pretty Printer

pprint :: ABE -> String
pprint (Num n) = show n
pprint (Boolean b) = show b
pprint (Mult n m) = "(" ++ pprint n ++ " * " ++ pprint m ++ ")"
pprint (Div n m) = "(" ++ pprint n ++ " / " ++ pprint m ++ ")"
pprint (Plus n m) = "(" ++ pprint n ++ " + " ++ pprint m ++ ")"
pprint (Minus n m) = "(" ++ pprint n ++ " - " ++ pprint m ++ ")"
pprint (And n m) = "(" ++ pprint n ++ " && " ++ pprint m ++ ")"
pprint (Leq n m) = "(" ++ pprint n ++ " <= " ++ pprint m ++ ")"
pprint (IsZero m) = "(isZero " ++ pprint m ++ ")"
pprint (If c n m) = "(if " ++ pprint c ++ " then " ++ pprint n ++ " else " ++ pprint m ++ ")"


-- Parser (Requires ParserUtils and Parsec)

expr :: Parser ABE
expr = buildExpressionParser opTable term

opTable = [ [ inFix "*" Mult AssocLeft
            , inFix "/" Div AssocLeft ]
          , [ inFix "+" Plus AssocLeft
            , inFix "-" Minus AssocLeft ]
          , [ inFix "<=" Leq AssocLeft
            , preFix "isZero" IsZero ]
          , [ inFix "&&" And AssocLeft ]
          ]

numExpr :: Parser ABE
numExpr = do i <- integer lexer
             return (Num (fromInteger i))

trueExpr :: Parser ABE
trueExpr = do i <- reserved lexer "true"
              return (Boolean True)

falseExpr :: Parser ABE
falseExpr = do i <- reserved lexer "false"
               return (Boolean False)

ifExpr :: Parser ABE
ifExpr = do reserved lexer "if"
            c <- expr
            reserved lexer "then"
            t <- expr
            reserved lexer "else"
            e <- expr
            return (If c t e)

term = parens lexer expr
       <|> numExpr
       <|> trueExpr
       <|> falseExpr
       <|> ifExpr

-- Parser invocation

parseABEM = parseM expr

parseABE = parseString expr

parseABEFile = parseFile expr

-- Evaluation Function

eval :: ABE -> Either String ABE
eval (Num x) = (Right (Num x))
eval (Plus t1 t2) =  let r1 = (eval t1)
                         r2 = (eval t2)
                      in case r1 of
                      -- Grabbed this from below. Thought the forwarding of Left r1 was
                      -- interesting.
                        (Left m) -> r1
                        (Right (Num v1)) -> case r2 of
                                              (Left m) -> r2
                                              (Right (Num v2)) -> (Right (Num (v1 + v2)))
                                              (Right _) -> (Left "Type Error in +")
                        (Right _) -> (Left "Type Error in +")

eval (Minus t1 t2) =  let r1 = (eval t1)
                          r2 = (eval t2)
                      in case r1 of
                        (Left m) -> r1
                        (Right (Num v1)) -> case r2 of
                                              (Left m) -> r2
                                              (Right (Num v2)) -> (Right (Num (v1 - v2)))
                                              (Right _) -> (Left "Type Error in -")
                        (Right _) -> (Left "Type Error in -")
eval (Mult t1 t2) = let r1 = (eval t1)
                        r2 = (eval t2)
                    in case r1 of
                      (Left m) -> r1
                      (Right (Num v1)) -> case r2 of
                                              (Left m) -> r2
                                              (Right (Num v2)) -> (Right (Num (v1 * v2)))
                                              (Right _) -> (Left "Type Error in *")
                      (Right _) -> (Left "Type Error in *")
eval (Div t1 t2) =  let r1 = (eval t1)
                        r2 = (eval t2)
                    in case r1 of
                      (Left m) -> r1
                      (Right (Num v1)) -> case r2 of
                                              (Left m) -> r2
                                              (Right (Num v2)) -> (Right (Num (div v1 v2)))
                                              (Right _) -> (Left "Type Error in /")
                      (Right _) -> (Left "Type Error in /")

eval (Boolean b) = (Right (Boolean b))
eval (And t1 t2) =  let r1 = (eval t1)
                        r2 = (eval t2)
                    in case r1 of 
                      (Left e) -> (Left e)
                      (Right (Boolean v1)) -> case r2 of
                                              (Left e) -> (Left e)
                                              (Right (Boolean v2)) -> (Right (Boolean (v1 && v2)))
                                              (Right _) -> (Left "Type error in &&")
                      (Right _) -> (Left "Type error in &&")

eval (Leq t1 t2) =  let r1 = (eval t1)
                        r2 = (eval t2)
                    in case r1 of
                      (Left e) -> (Left e)
                      (Right (Num v1)) -> case r2 of
                                            (Left e) -> (Left e)
                                            (Right (Num v2)) -> (Right (Boolean (v1 <= v2)))
                                            (Right _) -> (Left "Type error in <=")
                      (Right _) -> (Left "Type error in <=")


eval (IsZero t) = let r = (eval t)
                  in case r of
                    (Left e) -> r
                    (Right (Num v)) -> (Right (Boolean (v == 0)))
                    (Right _) -> (Left "Type error in isZero")
eval (If t1 t2 t3) =  let r = (eval t1)
                      in case r of
                        (Left _) -> r
                        (Right (Boolean v)) -> if v then (eval t2) else (eval t3)
                        (Right _) -> (Left "Type error in if")
-- Optimizer

optimize :: ABE -> ABE 
optimize (Plus t1 (Num 0)) = t1
optimize (Plus (Num 0) t2) = t2
optimize (If (Boolean True) t1 t2) = t1
optimize (If (Boolean False) t1 t2) = t2
optimize t = t

-- Type Derivation Function

typeof :: ABE -> Either String TABE
typeof (Num x) = (Right TNum)
typeof (Mult l r) = let l' = (typeof l)
                        r' = (typeof r)
                    in if l'==(Right TNum) && r'==(Right TNum)
                       then (Right TNum)
                       else Left "Type Mismatch in *"
typeof (Div l r) =  let l' = (typeof l)
                        r' = (typeof r)
                    in if l'==(Right TNum) && r'==(Right TNum)
                      then
                        case r of
                          (Num 0) -> (Left "Divide by zero error")
                          _ -> (Right TNum)
                      else
                        Left "Type Mismatch in /"
typeof (Plus l r) = let l' = (typeof l)
                        r' = (typeof r)
                    in if l'==(Right TNum) && r'==(Right TNum)
                       then (Right TNum)
                       else Left "Type Mismatch in +"
typeof (Minus l r) = let l' = (typeof l)
                         r' = (typeof r)
                     in if l'==(Right TNum) && r'==(Right TNum)
                        then (Right TNum)
                        else Left "Type Mismatch in -"
typeof (Boolean b) = (Right TBool)
typeof (And l r) = if (typeof l) == (Right TBool) && (typeof r) == (Right TBool)
                   then (Right TBool)
                   else Left "Type mismatch in &&"
typeof (Leq l r) = if (typeof l) == (Right TNum) && (typeof r) == (Right TNum)
                   then (Right TBool)
                   else Left "Type mismatch in <="
typeof (IsZero v) = if (typeof v) == (Right TNum)
                    then (Right TBool)
                    else Left "Type mismatch in IsZero"
typeof (If c t e) = if (typeof c) == (Right TBool)
                       && (typeof t)==(typeof e)
                    then (typeof t)
                    else Left "Type mismatch in if"


-- Interpreter

interp :: String -> Either String ABE
interp e =  let p=(parseABE e) in
              case (typeof p) of
                (Right _) ->  let v = eval (optimize p) in
                                case v of
                                  (Right x) -> (Right x)
                (Left l) -> (Left l)

               
