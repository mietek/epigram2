load TaggedInduction.pig;

idata Empty : Sig () -> Set := ;
infer Empty.Ind ;
idata One : Sig () -> Set := ('one : One _) ;
elab 'one : One _ ;
infer One.Ind ;
idata Nat : Sig () -> Set := ('zero : Nat _) ; ('suc : (n : Nat _) -> Nat _) ;
elab 'suc ('suc 'zero) : Nat _ ;
infer Nat.Ind ;
idata Vec (A : Set) : Nat _ -> Set := ('nil : Vec A 'zero) ; ('cons : A -> (n : Nat _) -> Vec A n -> Vec A ('suc n)) ;
make v := 'cons 'a ('suc 'zero) ('cons 'b 'zero 'nil) : Vec (Enum ['a 'b]) ('suc ('suc 'zero)) ;
elab v ;
infer Vec.Ind ;

let vtail (A : Set)(n : Nat _)(as : Vec A ('suc n)) : Vec A n ;
<= Vec.Case A ('suc n) as ;
define vtail A k ('cons a k as) := as ;
root ;
elab vtail (Enum ['a 'b]) ('suc 'zero) v ;
