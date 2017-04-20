{-# LANGUAGE GADTs #-}

module Proj3Utils where

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
-- "Project utilities for developing CFAE and CFBAE
-- interpreters."
--
-- Author: Dustin Horvath
-- Date: 20 April 2017
--
-- Base code pulled from http://ku-sldg.github.io/plih//haskell/proj3Utils.hs
-- and text http://ku-sldg.github.io/plih/
--

-- CFAE AST Definition

data CFAE where
  Num :: Int -> CFAE
  Plus :: CFAE -> CFAE -> CFAE
  Minus :: CFAE -> CFAE -> CFAE
  Mult :: CFAE -> CFAE -> CFAE
  Div :: CFAE -> CFAE -> CFAE
  Lambda :: String -> CFAE -> CFAE
  App :: CFAE -> CFAE -> CFAE
  Id :: String -> CFAE
  If0 :: CFAE -> CFAE -> CFAE -> CFAE
  --Including this here so that ex1 and ex2 can share the same data type.
  --Closure is not used by interpDynCFAE
  Closure :: String -> CFAE -> EnvS -> CFAE
  deriving (Show,Eq)


type Env = [(String,CFAE)]

-- Parser

expr :: Parser CFAE
expr = buildExpressionParser opTable term

opTable = [ [ inFix "*" Mult AssocLeft
            , inFix "/" Div AssocLeft ]
          , [ inFix "+" Plus AssocLeft
            , inFix "-" Minus AssocLeft ]
          ]

numExpr :: Parser CFAE
numExpr = do i <- integer lexer
             return (Num (fromInteger i))

identExpr :: Parser CFAE
identExpr = do i <- identifier lexer
               return (Id i)
              
lambdaExpr :: Parser CFAE
lambdaExpr = do reserved lexer "lambda"
                i <- identifier lexer
                reserved lexer "in"
                e <- expr
                return (Lambda i e)

appExpr :: Parser CFAE
appExpr = do reserved lexer "app"
             e1 <- expr
             e2 <- expr
             return (App e1 e2)

if0Expr :: Parser CFAE
if0Expr = do reserved lexer "if0"
             c <- expr
             reserved lexer "then"
             t <- expr
             reserved lexer "else"
             e <- expr
             return (If0 c t e)
            
             
term = parens lexer expr
       <|> numExpr
       <|> if0Expr
       <|> lambdaExpr
       <|> appExpr
       <|> identExpr
             
-- Parser invocation

parseCFAE = parseString expr

parseCFAEFile = parseFile expr


-- EXERCISE 1

--Note: this implementation doesn't provide much error checking
evalDynCFAE :: Env -> CFAE -> CFAE
evalDynCFAE env (Num x) = (Num x)

evalDynCFAE env (Plus t1 t2) = let (Num v1) = (evalDynCFAE env t1)
                                   (Num v2) = (evalDynCFAE env t2)
                              in (Num (v1+v2))
evalDynCFAE env (Minus t1 t2) = let (Num v1) = (evalDynCFAE env t1)
                                    (Num v2) = (evalDynCFAE env t2)
                                in (Num (v1-v2))
evalDynCFAE env (Mult t1 t2) = let (Num v1) = (evalDynCFAE env t1)
                                   (Num v2) = (evalDynCFAE env t2)
                               in (Num (v1*v2))
evalDynCFAE env (Div t1 t2) = let (Num v1) = (evalDynCFAE env t1)
                                  (Num v2) = (evalDynCFAE env t2)
                              in (Num (div v1 v2))
evalDynCFAE env (If0 t1 t2 t3) = let (Num v1) = (evalDynCFAE env t1)
                                     (Num v2) = (evalDynCFAE env t2)
                                     (Num v3) = (evalDynCFAE env t3)
                                 in case v1 of
                                   0 -> (Num v2)
                                   _ -> (Num v3)
evalDynCFAE env (Lambda i b) = (Lambda i b)
evalDynCFAE env (App f a) =  let (Lambda i b) = (evalDynCFAE env f)
                                 a' = (evalDynCFAE env a) 
                             in evalDynCFAE ((i,a'):env) b
evalDynCFAE env (Id id) = case (lookup id env) of
                            Just x -> x
                            Nothing -> error "Variable not found"

interpDynCFAE :: String -> CFAE
interpDynCFAE = (evalDynCFAE []) . parseCFAE

-- EXERCISE 2



-- Parser invocation


type EnvS = [(String,CFAEVal)]

-- Value type for closures
data CFAEVal where
  NumV :: Int -> CFAEVal
  ClosureV :: String -> CFAE -> EnvS -> CFAEVal
  deriving (Show,Eq)
-- NOTE: Sharing the datatype from CFAE so that parser can be shared as well


evalStatCFBE :: EnvS -> CFAE -> CFAEVal
evalStatCFBE cenv (Num x) = (NumV x)
evalStatCFBE cenv (Plus l r) = let (NumV l') = (evalStatCFBE cenv l)
                                   (NumV r') = (evalStatCFBE cenv r)
                               in (NumV (l'+r'))
evalStatCFBE cenv (Minus l r) = let (NumV l') = (evalStatCFBE cenv l)
                                    (NumV r') = (evalStatCFBE cenv r)
                                in (NumV (l'-r'))
evalStatCFBE cenv (Mult l r) = let (NumV l') = (evalStatCFBE cenv l)
                                   (NumV r') = (evalStatCFBE cenv r)
                                in (NumV (l' * r'))
evalStatCFBE cenv (Div l r) = let (NumV l') = (evalStatCFBE cenv l)
                                  (NumV r') = (evalStatCFBE cenv r)
                                in (NumV (div l' r'))
evalStatCFBE cenv (Lambda i b) = (ClosureV i b cenv)
evalStatCFBE cenv (App f a) = let (ClosureV i b e) = (evalStatCFBE cenv f)
                                  a' = (evalStatCFBE cenv a)
                              in evalStatCFBE ((i,a'):e) b
evalStatCFBE cenv (Id id) = case (lookup id cenv) of
                              Just x -> x
                              Nothing -> error "Variable not found"
evalStatCFBE cenv (If0 c t e) = let (NumV c') = (evalStatCFBE cenv c) in
                                  if c'==0 then (evalStatCFBE cenv t) else (evalStatCFBE cenv e)

-- We're getting values out at the end now
interpStatCFAE :: String -> CFAEVal
interpStatCFAE = (evalStatCFBE []) . parseCFAE

-- EXERCISE 3

-- CFBAE Parser

-- CFBAE AST Definition

data CFBAE where
  NumX :: Int -> CFBAE
  PlusX :: CFBAE -> CFBAE -> CFBAE
  MinusX :: CFBAE -> CFBAE -> CFBAE
  MultX :: CFBAE -> CFBAE -> CFBAE
  DivX :: CFBAE -> CFBAE -> CFBAE
  BindX :: String -> CFBAE -> CFBAE -> CFBAE
  LambdaX :: String -> CFBAE -> CFBAE
  AppX :: CFBAE -> CFBAE -> CFBAE
  IdX :: String -> CFBAE
  If0X :: CFBAE -> CFBAE -> CFBAE -> CFBAE
  deriving (Show,Eq)

-- Parser

exprX :: Parser CFBAE
exprX = buildExpressionParser opTableX termX

opTableX = [ [ inFix "*" MultX AssocLeft
            , inFix "/" DivX AssocLeft ]
          , [ inFix "+" PlusX AssocLeft
            , inFix "-" MinusX AssocLeft ]
          ]

numExprX :: Parser CFBAE
numExprX = do i <- integer lexer
              return (NumX (fromInteger i))

identExprX :: Parser CFBAE
identExprX = do i <- identifier lexer
                return (IdX i)

bindExprX :: Parser CFBAE
bindExprX = do reserved lexer "bind"
               i <- identifier lexer
               reservedOp lexer "="
               v <- exprX
               reserved lexer "in"
               e <- exprX
               return (BindX i v e)
              
lambdaExprX :: Parser CFBAE
lambdaExprX = do reserved lexer "lambda"
                 i <- identifier lexer
                 reserved lexer "in"
                 e <- exprX
                 return (LambdaX i e)

appExprX :: Parser CFBAE
appExprX = do reserved lexer "app"
              e1 <- exprX
              e2 <- exprX
              return (AppX e1 e2)

if0ExprX :: Parser CFBAE
if0ExprX = do reserved lexer "if0"
              c <- exprX
              reserved lexer "then"
              t <- exprX
              reserved lexer "else"
              e <- exprX
              return (If0X c t e)

termX = parens lexer exprX
       <|> numExprX
       <|> bindExprX
       <|> if0ExprX
       <|> lambdaExprX
       <|> appExprX
       <|> identExprX

-- Parser invocation

parseCFBAE = parseString exprX

parseCFBAEFile = parseFile exprX

elabCFBAE :: CFBAE -> CFAE
elabCFBAE (NumX n) = (Num n)
elabCFBAE (PlusX l r) = (Plus (elabCFBAE l) (elabCFBAE r))
elabCFBAE (MinusX l r) = (Minus (elabCFBAE l) (elabCFBAE r))
elabCFBAE (MultX l r) = (Mult (elabCFBAE l) (elabCFBAE r))
elabCFBAE (DivX l r) = (Div (elabCFBAE l) (elabCFBAE r))
elabCFBAE (BindX x v b) = (App (Lambda x (elabCFBAE b)) (elabCFBAE v))
elabCFBAE (IdX x) = (Id x)
elabCFBAE (LambdaX x b) = (Lambda x (elabCFBAE b))
elabCFBAE (AppX b v) = (App (elabCFBAE b) (elabCFBAE v))
elabCFBAE (If0X c t e) = (If0 (elabCFBAE c) (elabCFBAE t) (elabCFBAE e))

-- ClosureV "x" (Plus (Id "x") (Num 1)) []

prelude = [ 
            ("inc", ClosureV "x" (Plus (Id "x") (Num 1)) []) ,
            ("dec", ClosureV "x" (Minus (Id "x") (Num 1)) [])
          ]

interpCFBAE :: String -> CFAEVal
--interpCFBAE = (evalCFBAE prelude) . parseCFBAE
interpCFBAE = ((evalStatCFBE prelude) . (elabCFBAE)) . parseCFBAE





