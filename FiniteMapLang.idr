module FiniteMapLang

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

data ExtendStore : (s : Store) -> (s' : Store) -> Type where 
    MkExt : (s : Store) -> (v : Var) -> (p : Not (ElemStore v s)) 
            -> ExtendStore s ((v,Z)::s)

data UpdateStore : (s : Store) -> (s' : Store) -> Type where 
    MkUp : (s : Store) -> (k : Var) -> (v : Nat)
        -> (p : ElemStore k s) 
        -> UpdateStore s (update k v s p) 
        
data Expr : (store : Store) -> Type where
    MkVar : (v : Var) -> (store : Store) 
        ->  (prf : ElemStore v store) -> Expr store 
    MkNum : Nat -> (s : Store) -> Expr s 
    MkAdd : (s : Store) -> Expr s -> Expr s -> Expr s 
    MkMul : (s : Store) -> Expr s -> Expr s -> Expr s 

data Stmt : (s : Store) -> (s' : Store) -> Type where 
    MkSeq : (s1 : Stmt s s') -> (s2 : Stmt s' s'')
          -> Stmt s s'' 
    MkExpr : (s : Store) -> (e : Expr s) -> Stmt s s
    MkDec  : (s : Store) -> (v : Var) -> (prf : Not (ElemStore v s))
          -> (s' : Store) -> (sP : ExtendStore s s') ->  Stmt s s'
    MkAss  : (s : Store) -> (v : Var) -> (e : Expr s) 
          -> (prf : ElemStore v s)
          -> (s' : Store)
          -> (sP : UpdateStore s s')
          -> Stmt s s'




eval : Expr s -> Nat
eval (MkVar v s p) = lookup v s p
eval (MkNum n s) = n 
eval (MkAdd s e1 e2) = eval e1 + eval e2
eval (MkMul s e1 e2) = eval e1 + eval e2
