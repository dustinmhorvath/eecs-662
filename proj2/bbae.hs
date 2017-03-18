{-# LANGUAGE GADTs #-}

module Proj2Utils where

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

-- Doing a BAD
import System.IO.Unsafe

--
-- Simple caculator with variables extended Booleans and both static and
-- dynamic type checking.
--
-- Author: Perry Alexander
-- Date: Wed Jul 13 11:24:46 CDT 2016
--
-- Source files for the Boolean Binding Arithmetic Expressions (BBAE)
-- language from PLIH
--

-- BBAE AST Definition

type Env = [(String,BBAE)]
type Cont = [(String,TBBAE)]

data TBBAE where
  TNum :: TBBAE
  TBool :: TBBAE
  deriving (Show,Eq)

data BBAE where
  Num :: Int -> BBAE
  Plus :: BBAE -> BBAE -> BBAE
  Minus :: BBAE -> BBAE -> BBAE
  Bind :: String -> BBAE -> BBAE -> BBAE
  Id :: String -> BBAE
  Boolean :: Bool -> BBAE
  And :: BBAE -> BBAE -> BBAE
  Leq :: BBAE -> BBAE -> BBAE
  IsZero :: BBAE -> BBAE
  If :: BBAE -> BBAE -> BBAE -> BBAE
  Seq :: BBAE -> BBAE -> BBAE
  Print :: BBAE -> BBAE
  Cons :: BBAE -> BBAE -> BBAE
  First :: BBAE -> BBAE
  Rest :: BBAE -> BBAE
  IsEmpty :: BBAE -> BBAE
  Empty :: BBAE
  deriving (Show,Eq)



-- Parser

expr :: Parser BBAE
expr = buildExpressionParser opTable term

opTable = [ [ inFix "+" Plus AssocLeft
              , inFix "-" Minus AssocLeft ]
          , [ inFix "<=" Leq AssocLeft
            , preFix "isZero" IsZero ]
          , [ inFix "&&" And AssocLeft ]
          ]

numExpr :: Parser BBAE
numExpr = do i <- integer lexer
             return (Num (fromInteger i))

identExpr :: Parser BBAE
identExpr = do i <- identifier lexer
               return (Id i)

bindExpr :: Parser BBAE
bindExpr = do reserved lexer "bind"
              i <- identifier lexer
              reservedOp lexer "="
              v <- expr
              reserved lexer "in"
              e <- expr
              return (Bind i v e)

trueExpr :: Parser BBAE
trueExpr = do i <- reserved lexer "true"
              return (Boolean True)

falseExpr :: Parser BBAE
falseExpr = do i <- reserved lexer "false"
               return (Boolean False)

ifExpr :: Parser BBAE
ifExpr = do reserved lexer "if"
            c <- expr
            reserved lexer "then"
            t <- expr
            reserved lexer "else"
            e <- expr
            return (If c t e)
            
seqExpr :: Parser BBAE
seqExpr = do reserved lexer "seq"
             f <- expr
             s <- expr
             return (Seq f s)

printExpr :: Parser BBAE
printExpr = do reserved lexer "print"
               t <- expr
               return (Print t)

consExpr :: Parser BBAE
consExpr = do reserved lexer "cons"
              f <- expr
              s <- expr
              return (Cons f s)

firstExpr :: Parser BBAE
firstExpr = do reserved lexer "first"
               t <- expr
               return (First t)
             
restExpr :: Parser BBAE
restExpr = do reserved lexer "rest"
              t <- expr
              return (Rest t)

isEmptyExpr :: Parser BBAE
isEmptyExpr = do reserved lexer "isEmpty"
                 t <- expr
                 return (IsEmpty t)

emptyExpr :: Parser BBAE
emptyExpr = do reserved lexer "empty"
               return Empty
             
term = parens lexer expr
       <|> numExpr
       <|> bindExpr
       <|> trueExpr
       <|> falseExpr
       <|> ifExpr
       <|> consExpr
       <|> firstExpr
       <|> restExpr              
       <|> isEmptyExpr
       <|> emptyExpr
       <|> printExpr
       <|> seqExpr
       -- Oddly enough, I had problems with identExpr when it was farther up
       -- the list
       <|> identExpr
       

-- Parser invocation

parseBBAE = parseString expr

parseBBAEFile = parseFile expr


eval :: Env -> BBAE -> Either String BBAE
eval env (Num x) = (Right (Num x))
eval env (Boolean b) = (Right (Boolean b))
eval env (Plus l r) = let l' = (eval env l)
                          r' = (eval env r)
                      in case l' of
                        (Left m) -> l'
                        (Right (Num v1)) -> case r' of
                                              (Left m) -> r'
                                              (Right (Num v2)) -> (Right (Num (v1+v2)))
                                              (Right _) -> Left "Type error in +"
                        (Right _) -> (Left "Type error in +")
eval env (Minus l r) =  let l' = (eval env l)
                            r' = (eval env r)
                        in case l' of
                          (Left m) -> l'
                          (Right (Num v1)) -> case r' of
                                                (Left m) -> r'
                                                (Right (Num v2)) -> (Right (Num (v1 - v2)))
                                                (Right _) -> (Left "Type Error in -")
                          (Right _) -> (Left "Type Error in -")
eval env (Bind i v b) = let v' = (eval env v)
                        in case v' of 
                          (Right v') -> (eval ((i,v'):env) b)
                          (Left _) -> v'
eval env (Id id) = case (lookup id env) of
                     (Just x) -> (Right x)
                     (Nothing) -> (Left "Eval ID: Variable not found")
eval env (And l r) =  let l' = (eval env l)
                          r' = (eval env r)
                      in case l' of
                        (Left e) -> (Left e)
                        (Right (Boolean v1)) -> case r' of
                                                  (Left e) -> (Left e)
                                                  (Right (Boolean v2)) -> (Right (Boolean (v1 && v2)))
                                                  (Right _) -> (Left "Type error in &&")
                        (Right _) -> (Left "Type error in &&")
eval env (Leq l r) =  let l' = (eval env l)
                          r' = (eval env r)
                      in case l' of 
                        (Left e) -> (Left e)
                        (Right (Num v1)) -> case r' of
                                              (Left e) -> (Left e)
                                              (Right (Num v2)) -> (Right (Boolean (v1 <= v2)))
                                              (Right _) -> (Left "Type error in <=")
                        (Right _) -> (Left "Type error in <=")
eval env (IsZero v) = let v' = (eval env v)
                      in case v' of
                        (Left e) -> v'
                        (Right (Num v)) -> (Right (Boolean (v == 0)))
                        (Right _) -> (Left "Type error in isZero")
eval env (If c t e) = let c' = (eval env c)
                      in case c' of
                        (Left _) -> c'
                        (Right (Boolean v)) -> if v then (eval env t) else (eval env e)
                        (Right _) -> (Left "Type error in if")

eval env (Seq t1 t2) = seq (eval env t1) (eval env t2)
eval env (Print t) = --let t' = eval env t in
                       (eval env (seq (unsafePerformIO (print t)) (Num 0)))



eval env (Empty) = (Right Empty)
eval env (IsEmpty l) =  let (Right l') = eval env l 
                        in case l' of
                          (Empty) -> (Right (Boolean True))
                          _ -> (Right (Boolean False))
eval env (First l) =  let (Right l') = eval env l 
                      in case l' of
                        (Cons f r) -> (Right f)
                        _ -> (Left "Not valid list")
eval env (Rest l) = let (Right l') = eval env l
                    in case l' of
                      (Cons f r) -> (Right r)
                      _ -> (Left "Not valid list")

eval env (Cons f r) = do {
                        f' <- eval env f;
                        r' <- eval env r;
                        return (Cons f' r');
                        -- I don't *think* error handling is needed here? =/
                      }





-- bind with subst machinery below here

subst :: String -> BBAE -> BBAE -> BBAE
subst _ _ (Num x) = (Num x)
subst i v (Plus l r) = (Plus (subst i v l) (subst i v r))
subst i v (Minus l r) = (Minus (subst i v l) (subst i v r))
subst i v (Bind i' v' b') = if i==i'
	                        then (Bind i' (subst i v v') b')
	                        else (Bind i' (subst i v v') (subst i v b'))
subst i v (Id i') = if i==i'
	                then v
	                else (Id i')

evals :: BBAE -> Either String BBAE
evals (Num x) = Right (Num x)
evals (Plus l r) =  let l' = (evals l)
                        r' = (evals r)
                    in case l' of
                      (Left _) -> l'
                      (Right (Num v1)) -> case r' of
                                            (Left e) -> (Left e)
                                            (Right (Num v2)) -> (Right (Num (v1+v2)))
                                            (Right _) -> (Left "Type error in +")
                      (Right _) -> (Left "Type error in +")
evals (Minus l r) = let l' = (evals l)
                        r' = (evals r)
                    in case l' of
                      (Left _) -> l'
                      (Right (Num v1)) -> case r' of
                                            (Left e) -> (Left e)
                                            (Right (Num v2)) -> (Right (Num (v1-v2)))
                                            (Right _) -> (Left "Type error in -")
                      (Right _) -> (Left "Type error in -")
evals (Bind i v b) =  let v' = evals v
                      in case v' of
                        (Left _) -> v'
                        (Right arg) -> (evals (subst i arg b))
evals (Id id) = (Left "Undeclared Variable")

interp :: String -> (Either String BBAE)
interps = evals . parseBBAE
interp = (eval []) . parseBBAE



-- Typing

typeof :: Cont -> BBAE -> Either String TBBAE

typeof cont (Num x) = (Right TNum)
typeof cont (Plus l r) = let l' = (typeof cont l)
                             r' = (typeof cont r)
                         in if l'==(Right TNum) && r'==(Right TNum)
                            then (Right TNum)
                            else (Left "Type Mismatch in +")
typeof cont (Minus l r) = let l' = (typeof cont l)
                              r' = (typeof cont r)
                          in if l'==(Right TNum) && r'==(Right TNum)
                             then (Right TNum)
                             else (Left "Type Mismatch in -")
typeof cont (Bind i v b) = let v' = typeof cont v in
                             case v' of
                               (Right v'') -> typeof ((i,v''):cont) b
                               (Left _) -> v'
typeof cont (Id id) = case (lookup id cont) of
                        Just x -> (Right x)
                        Nothing -> (Left "Varible not found")
typeof cont (Boolean b) = (Right TBool)
typeof cont (And l r) = if (typeof cont l) == (Right TBool)
                           && (typeof cont r) == (Right TBool)
                        then (Right TBool)
                        else (Left "Type mismatch in &&")
typeof cont (Leq l r) = if (typeof cont l) == (Right TNum)
                           && (typeof cont r) == (Right TNum)
                        then (Right TBool)
                        else (Left "Type mismatch in <=")
typeof cont (IsZero v) = if (typeof cont v) == (Right TNum)
                         then (Right TBool)
                         else (Left "Type mismatch in IsZero")
typeof cont (If c t e) = if (typeof cont c) == (Right TBool)
                            && (typeof cont t)==(typeof cont e)
                         then (typeof cont e)
                         else (Left "Type mismatch in if")



