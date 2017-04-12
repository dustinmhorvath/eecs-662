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
-- Project utilities for developing CFAE and CFBAE
-- interpreters.
--
-- Author: Perry Alexander
-- Date: 6 April 2017
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
  deriving (Show,Eq)


type Env = [(String,CFAE)]
--type Cont = [(String,TFBAE)]

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
       <|> identExpr
       <|> if0Expr
       <|> lambdaExpr
       <|> appExpr
             
-- Parser invocation

parseCFAE = parseString expr

parseCFAEFile = parseFile expr


-- EXERCISE 1

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
                            Nothing -> error "Varible not found"

interpDynCFAE :: String -> CFAE
interpDynCFAE = (evalDynCFAE []) . parseCFAE

-- EXERCISE 2


-- Parser

-- CFAEb AST Definition

data CFAEb where
  CNum :: Int -> CFAEb
  CPlus :: CFAEb -> CFAEb -> CFAEb
  CMinus :: CFAEb -> CFAEb -> CFAEb
  CMult :: CFAEb -> CFAEb -> CFAEb
  CDiv :: CFAEb -> CFAEb -> CFAEb
  CBind :: String -> CFAEb -> CFAEb -> CFAEb
  CLambda :: String -> CFAEb -> CFAEb
  CApp :: CFAEb -> CFAEb -> CFAEb
  CId :: String -> CFAEb
  CIf :: CFAEb -> CFAEb -> CFAEb -> CFAEb
  Closure :: String -> CFAEb -> CEnv -> CFAEb
  deriving (Show,Eq)

exprC :: Parser CFAEb
exprC = buildExpressionParser opTableC termC

opTableC = [ [ inFix "*" CMult AssocLeft
             , inFix "/" CDiv AssocLeft ]
           , [ inFix "+" CPlus AssocLeft
             , inFix "-" CMinus AssocLeft ]
           ]

numExprC :: Parser CFAEb
numExprC = do i <- integer lexer
              return (CNum (fromInteger i))

identExprC :: Parser CFAEb
identExprC = do i <- identifier lexer
                return (CId i)

bindExprC :: Parser CFAEb
bindExprC = do reserved lexer "bind"
               i <- identifier lexer
               reservedOp lexer "="
               v <- exprC
               reserved lexer "in"
               e <- exprC
               return (CBind i v e)
              
lambdaExprC :: Parser CFAEb
lambdaExprC = do reserved lexer "lambda"
                 i <- identifier lexer
                 reserved lexer "in"
                 e <- exprC
                 return (CLambda i e)

appExprC :: Parser CFAEb
appExprC = do reserved lexer "app"
              e1 <- exprC
              e2 <- exprC
              return (CApp e1 e2)

ifExprC :: Parser CFAEb
ifExprC = do reserved lexer "if"
             c <- exprC
             reserved lexer "then"
             t <- exprC
             reserved lexer "else"
             e <- exprC
             return (CIf c t e)
            
             
termC = parens lexer exprC
        <|> numExprC
        <|> identExprC
        <|> bindExprC
        <|> ifExprC
        <|> lambdaExprC
        <|> appExprC
             
-- Parser invocation

parseCFAEb = parseString exprC

parseCFAEbFile = parseFile exprC


type CEnv = [(String,CFAEbVal)]

data CFAEbVal where
  NumV :: Int -> CFAEbVal
  ClosureV :: String -> CFAEb -> CEnv -> CFAEbVal
  deriving (Show,Eq)


evalStatCFBE :: CEnv -> CFAEb -> CFAEbVal
evalStatCFBE cenv (CNum x) = (NumV x)
evalStatCFBE cenv (CPlus l r) = let (NumV l') = (evalStatCFBE cenv l)
                                    (NumV r') = (evalStatCFBE cenv r)
                                in (NumV (l'+r'))
evalStatCFBE cenv (CMinus l r) = let (NumV l') = (evalStatCFBE cenv l)
                                     (NumV r') = (evalStatCFBE cenv r)
                                 in (NumV (l'-r'))
evalStatCFBE cenv (CLambda i b) = (ClosureV i b cenv)
evalStatCFBE cenv (CApp f a) = let (ClosureV i b e) = (evalStatCFBE cenv f)
                                   a' = (evalStatCFBE cenv a)
                               in evalStatCFBE ((i,a'):e) b
evalStatCFBE cenv (CId id) = case (lookup id cenv) of
                               Just x -> x
                               Nothing -> error "Varible not found"
evalStatCFBE cenv (CIf c t e) = let (NumV c') = (evalStatCFBE cenv c) in
                                  if c'==0 then (evalStatCFBE cenv t) else (evalStatCFBE cenv e)

-- We're getting values out at the end now
interpStatCFAEb :: String -> CFAEbVal
interpStatCFAEb = (evalStatCFBE []) . parseCFAEb



-- EXERCISE 3

--exprX :: Parser CCFAE
--exprX = buildExpressionParser opTableX termX
--
--opTableX = [ [ inFix "*" MultX AssocLeft
--            , inFix "/" DivX AssocLeft ]
--          , [ inFix "+" PlusX AssocLeft
--            , inFix "-" MinusX AssocLeft ]
--          ]
--
--numExprX :: Parser CCFAE
--numExprX = do i <- integer lexer
--              return (NumX (fromInteger i))
--
--identExprX :: Parser CCFAE
--identExprX = do i <- identifier lexer
--                return (IdX i)
--
--bindExprX :: Parser CCFAE
--bindExprX = do reserved lexer "bind"
--               i <- identifier lexer
--               reservedOp lexer "="
--               v <- exprX
--               reserved lexer "in"
--               e <- exprX
--               return (BindX i v e)
--              
--lambdaExprX :: Parser CCFAE
--lambdaExprX = do reserved lexer "lambda"
--                 i <- identifier lexer
--                 reserved lexer "in"
--                 e <- exprX
--                 return (LambdaX i e)
--
--appExprX :: Parser CCFAE
--appExprX = do reserved lexer "app"
--              e1 <- exprX
--              e2 <- exprX
--              return (AppX e1 e2)
--
--ifExprX :: Parser CCFAE
--ifExprX = do reserved lexer "if"
--             c <- exprX
--             reserved lexer "then"
--             t <- exprX
--             reserved lexer "else"
--             e <- exprX
--             return (IfX c t e)
--            
--             
--termX = parens lexer exprX
--       <|> numExprX
--       <|> identExprX
--       <|> bindExprX
--       <|> ifExprX
--       <|> lambdaExprX
--       <|> appExprX
--             
---- Parser invocation
--
----parseCCFAE = parseString exprX
--
----parseCCFAEFile = parseFile exprX
--
