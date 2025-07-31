module FiniteMapLang3

import Data.List

Key : Type
Key = Nat 

-- Store : {a : Type} -> Type 
-- Store {a} = List (Key, a)

-- abandoning 
-- need a type

data Store : (a : Type) -> Type where 
    MkStoreNil : Store a
    MkStore : (Key, a) -> Store a -> Store a 

Var : Type 
Var = Nat 

data ElemStore : Nat -> (s : Store a) -> Type where
  SHere : ElemStore x (MkStore (x, v) xs)
  SThere : ElemStore x s -> ElemStore x (MkStore (y,v) s)
 
lookup : {a : Type} -> (v : Key) -> (s : Store a) 
      -> (prf : ElemStore v s) -> a 
lookup v MkStoreNil SHere impossible
lookup v MkStoreNil (SThere p) impossible
lookup v (MkStore (v,v1) s) SHere = v1 
lookup {a} v (MkStore (k,v2) s) (SThere p) = lookup {a} v s p

-- type of Var to change to a 
insert : {a : Type} -> (k : Key) -> (v : a) -> (s : Store a) 
  -> (prf : Not (ElemStore k s)) -> Store a
insert k v MkStoreNil prf = MkStore (k,v) MkStoreNil
insert k v xs prf = MkStore (k,v) xs

update : (k : Var) -> (v : a) -> (s : Store a)
  -> (prf : ElemStore k s) -> Store a
update k v MkStoreNil SHere impossible
update k v MkStoreNil (SThere p) impossible
update k v (MkStore (k,v1) s) SHere = MkStore (k, v) s  
update k v (MkStore (k2,v2) s) (SThere p) = MkStore (k2, v2) (update k v s p )

-- a must unify with Nat here as we extend the store with a Z
data ExtendStore : (s : Store a) -> (s' : Store a) -> Type where 
    MkExt : (s : Store Nat) -> (v : Var) -> (p : Not (ElemStore v s)) 
            -> ExtendStore s (MkStore (v,Z) s)

data UpdateStore : (s : Store a) -> (s' : Store a) -> Type where 
    MkUp : (s : Store a) -> (k : Var) -> (v : a)
        -> (p : ElemStore k s) 
        -> UpdateStore s (update k v s p) 
        
data Expr : (store : Store a) -> Type where
    MkVar : (v : Var) -> (store : Store a) 
        ->  (prf : ElemStore v store) -> Expr store 
    MkNum : Nat -> (s : Store a) -> Expr s 
    MkAdd : (s : Store a) -> Expr s -> Expr s -> Expr s 
    MkMul : (s : Store a) -> Expr s -> Expr s -> Expr s 

evalE : {s : Store Nat} -> Expr s -> Nat
evalE (MkVar v s p) = lookup v s p
evalE (MkNum n s) = n 
evalE (MkAdd s e1 e2) = evalE e1 + evalE e2
evalE (MkMul s e1 e2) = evalE e1 + evalE e2


data Stmt : (s : Store a) -> (s' : Store a) -> Type where 
    MkSeq : (s1 : Stmt s s') -> (s2 : Stmt s' s'')
          -> Stmt s s'' 
    MkDec  : (s : Store Nat) -> (v : Var) -> (prf : Not (ElemStore v s))
          -> Stmt s (insert v Z s prf)
    MkAss  : (s : Store Nat) -> (v : Var) -> (e : Expr s) 
          -> (prf : ElemStore v s)
         -- -> (s' : Store)
         -- -> (sP : UpdateStore s s')
          -> Stmt s (update v (evalE e) s prf)


data Result : Store Nat -> Type where 
    MkResult : (s : Store Nat) -> Result s

evalS : (s: Store Nat) -> Stmt s s' -> Result s'
evalS s (MkSeq s1 s2) = 
    case evalS s s1 of 
        MkResult s1' => evalS s1' s2
evalS s (MkDec s v prf) = MkResult (insert v Z s prf)
evalS s (MkAss s v e prf) = MkResult (update v (evalE e) s prf)
    