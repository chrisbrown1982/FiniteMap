module FiniteMap 

data AssocList : (a : Type) -> (b : Type) -> Type where 
    ANil  : AssocList a b 
    ACons : (a, b) -> AssocList a b -> AssocList a b
 
lookup : Eq a =>  a -> AssocList a b -> Maybe b 
lookup key ANil = Nothing 
lookup key (ACons (k,v) xs) with (k == key) 
    lookup key (ACons (k,v) xs) | True = Just v 
    lookup key (ACons (k,v) xs) | False = lookup key xs

insert : a -> b -> AssocList a b -> AssocList a b 
insert key value list = ACons (key, value) list 

exampleMap : AssocList Nat String 
exampleMap = insert 1 "one" (insert 2 "two" ANil)

testLookup : Maybe String 
testLookup = lookup 1 exampleMap