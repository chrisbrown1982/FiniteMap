module FiniteMap3

import Data.List
import Data.List.Elem
import Data.So

-- Store : Type 
-- Store = List (Nat, Nat)

Var : Type 
Var = Nat 

data Support : Type where 
    MkSup : (xs : List Var) -> (prf : So (sorted xs)) -> Support

data ElemSupport : (v : Var) -> Support -> Type where
    MkES : Elem v xs -> ElemSupport v (MkSup xs prf)

data Store : Support -> Type where
    SNil  : Store s
    SCons : (x : Var) -> (v : Nat) -> ElemSupport x s -> Store s -> Store s

data ElemStore : Var -> (s : Store vs) -> Type where
  SHere : ElemStore x (SCons x v p xs)
  SThere : ElemStore x xs -> ElemStore x (SCons y v p xs)

lookup : (v : Var) -> (s : Store vs) -> (prf : ElemStore v s) -> Nat 
lookup v SNil SHere impossible
lookup v SNil (SThere p) impossible
lookup v (SCons v v1 p xs) SHere = v 
lookup v (SCons k v2 p xs) (SThere q) = lookup v xs q

lem1 : {x : Nat} -> So (sorted (x :: xs)) -> So (sorted xs)

lookupSup : (v : Var) -> (s : Support) -> (prf : ElemSupport v s) -> Nat 
lookupSup v (MkSup [] _) (MkES Here) impossible
lookupSup v (MkSup [] _) (MkES (There p)) impossible
lookupSup v (MkSup (v::s) _) (MkES Here) = v 
lookupSup v (MkSup (k::s) prf) (MkES (There p)) = lookupSup v (MkSup s (lem1 prf)) (MkES p) 
 

insert : (k : Var) -> (v : Nat) -> (s : Store vs) -> (prf : ElemSupport k vs) -> Store vs
insert k v SNil prf = SCons k v prf SNil
insert k v xs prf = SCons k v prf xs

lem2 : (v : Var) -> (vs : List Var) -> So (sorted vs) -> So (sorted (sort (v :: vs)))
lem3 : (v : Var) -> (vs : List Var) -> So (sorted (sort (v :: vs))) -> So (sorted (v :: vs))

addVars : (k : Var) -> (vars : Support) -> Support 
addVars k (MkSup vars prf) = MkSup (sort (k :: vars)) (lem2 k vars prf)
 
inStoreInVars : (k : Var) -> (s : Store vs) -> ElemStore k s -> ElemSupport k vs

update : (k : Var) -> (v : Nat) -> (s : Store vs) -> (prf : ElemStore k s) -> Store vs
update k v SNil SHere impossible
update k v SNil (SThere p) impossible
update k v (SCons k v1 p xs) SHere = SCons k v p xs  
update k v (SCons k2 v2 p xs) (SThere q) = SCons k2 v2 p (update k v xs q)

data Expr : (store : Support) -> Type where
    MkVar : (v : Var) -> (vars : Support) 
        ->  (prf : ElemSupport v vars) -> Expr vars 
    MkNum : Nat -> (s : Support) -> Expr s 
    MkAdd : (s : Support) -> Expr s -> Expr s -> Expr s 
    MkMul : (s : Support) -> Expr s -> Expr s -> Expr s 

evalE : Expr s -> Nat
evalE (MkVar v s p) = lookupSup v s p
evalE (MkNum n s) = n 
evalE (MkAdd s e1 e2) = evalE e1 + evalE e2
evalE (MkMul s e1 e2) = evalE e1 + evalE e2


data Stmt : (s : Support) -> (s' : Support) -> Type where 
    MkSeq : {s1 : Support} -> (p1 : Stmt s0 s1) -> (p2 : Stmt s1 s2) -> Stmt s0 s2 
    MkDec  : (vars : Support) -> (v : Var)
          -> Stmt vars (addVars v vars)
    MkAss  : (s : Support) -> (v : Var) -> (e : Expr s) 
          -> (prf : ElemSupport v s)
          -> Stmt s s

weakenSt : (v : Var) -> (vs : List Var) -> (prf : So (sorted vs))
        -> (s : Store (MkSup vs prf)) -> Store (MkSup (v :: vs) (lem3 v vs (lem2 v vs prf)))
weakenSt v vs prf SNil = SNil
weakenSt v vs prf0 (SCons k v2 prf xs) = ?h -- let indH = (weakenSt v xs) in  -- SCons k v2 (There prf) indH

{-
evalS : (s: Support) -> Stmt s s' -> Store s -> Store s'
evalS s (MkSeq {s1} p1 p2) st = case evalS s p1 st of
    x => evalS s1 p2 x
evalS s (MkDec s v) st = weakenSt v st
evalS s (MkAss s v e prf) st = insert v (evalE e) st prf 

-------------

data IsDec : (Stmt s s') -> (v1, v2 : Var) -> Type where 
    MkIsDec : IsDec (MkSeq (MkDec s1 v1)
                           (MkDec (addVars v1 s1) v2)) v1 v2

-- p1 = d1;d2
-- p2 = d2;d1

comm : (v1, v2 : Var) -> (s : Support) -> (st : Store s) 
    -> (p1 : Stmt s s1) -> (p2 : Stmt s s2) -> IsDec p1 v1 v2 -> IsDec p2 v2 v1 -> evalS s p1 st = evalS s p2 st
comm v1 v2 s1 st (MkSeq (MkDec s1 v1) (MkDec (addVars v1 s1) v2)) 
                 (MkSeq (MkDec s1 v2) (MkDec (addVars v2 s1) v1)) MkIsDec MkIsDec =
                    case st of 
                        SNil => ?h1
                        SCons k v3 prf xs => ?h2

-- sort list for normal form
-}
