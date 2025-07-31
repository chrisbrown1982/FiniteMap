module FiniteMap2

import Data.List

Store : Type 
Store = List (Nat, Nat)

Var : Type 
Var = Nat 

data ElemStore : Nat -> (s : Store) -> Type where
  SHere : ElemStore x ((x, v)::xs)
  SThere : ElemStore x s -> ElemStore x ((y,v)::s)

lookup : (v : Var) -> (s : Store) 
  -> (prf : ElemStore v s) -> Nat 
lookup v [] SHere impossible
lookup v [] (SThere p) impossible
lookup v ((v,v1)::s) SHere = v 
lookup v ((k,v2)::s) (SThere p) = lookup v s p 

insert : (k : Var) -> (v : Nat) -> (s : Store) 
  -> (prf : Not (ElemStore k s)) -> Store
insert k v [] prf = [(k,v)]
insert k v xs prf = (k,v) :: xs

update : (k : Var) -> (v : Nat) -> (s : Store)
  -> (prf : ElemStore k s) -> Store 
update k v [] SHere impossible
update k v [] (SThere p) impossible
update k v ((k,v1)::s) SHere = (k, v)::s  
update k v ((k2,v2)::s) (SThere p) = (k2, v2) :: update k v s p 

data Expr : (store : Store) -> Type where
    MkVar : (v : Var) -> (store : Store) 
        ->  (prf : ElemStore v store) -> Expr store 
    MkNum : Nat -> (s : Store) -> Expr s 
    MkAdd : (s : Store) -> Expr s -> Expr s -> Expr s 
    MkMul : (s : Store) -> Expr s -> Expr s -> Expr s 

evalE : Expr s -> Nat
evalE (MkVar v s p) = lookup v s p
evalE (MkNum n s) = n 
evalE (MkAdd s e1 e2) = evalE e1 + evalE e2
evalE (MkMul s e1 e2) = evalE e1 + evalE e2


data Stmt : (s : Store) -> (s' : Store) -> Type where 
    MkSeq : (s1 : Stmt s s') -> (s2 : Stmt s' s'')
          -> Stmt s s'' 
    MkDec  : (s : Store) -> (v : Var) -> (prf : Not (ElemStore v s))
          -> Stmt s (insert v Z s prf)
    MkAss  : (s : Store) -> (v : Var) -> (e : Expr s) 
          -> (prf : ElemStore v s)
          -> Stmt s (update v (evalE e) s prf)


data Result : Store -> Type where 
    MkResult : (s : Store) -> Result s

evalS : (s: Store) -> Stmt s s' -> Result s'
evalS s (MkSeq s1 s2) = 
    case evalS s s1 of 
        MkResult s1' => evalS s1' s2
evalS s (MkDec s v prf) = MkResult (insert v Z s prf)
evalS s (MkAss s v e prf) = MkResult (update v (evalE e) s prf)

data IsDec : (Stmt s s') -> (v1, v2 : Var) -> Type where 
    MkIsDec : IsDec (MkSeq (MkDec s1 v1 p1)
                           (MkDec (insert v1 Z s1 p1) v2 p2)) v1 v2

-- p1 = d1;d2
-- p2 = d2;d1

commDec : (v1, v2 : Var) -> (s : Store)
       -> (p1 : Stmt s s1) -> (p2 : Stmt s s2) -> IsDec p1 v1 v2 -> IsDec p2 v2 v1 -> s1 = s2
commDec v1 v2 s
        (MkSeq (MkDec s v1 p1') (MkDec (insert v1 0 s p1') ?h2 ?p2))
        -- (MkSeq (MkDec s1 v1 p1) (MkDec (insert v1 Z s1 p1) v2 p2)) 
        q1 MkIsDec q1' = ?h
        -- (MkSeq (MkDec s1 v2 p3) (MkDec (insert v2 Z s1 p3) v1 p4)) MkIsDec MkIsDec = ?h

     