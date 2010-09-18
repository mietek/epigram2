load TaggedInduction.pig ;

let idescInduction (I : Set)
		   (x : IDesc I)
      		   (P : IDesc I -> Set)
		   (pf-Pi : :- ((E : EnumU)
	                        (T : Enum E -> IDesc I) => 
			        (((: Set) (P ('piD (Enum E) T))) == ((: Set) (P ('fpiD E T))))))
		   (pf-Sigma : :- ((E : EnumU)
		   	           (T : branches E (\ _ -> IDesc I)) =>
			           (((: Set) (P ('sigmaD (Enum E) (\ x -> switch E x (\ _ -> IDesc I) T)))) == ((: Set) (P ('fsigmaD E T))))))
		   (pf-Prod : :- ((x : IDesc I)
		   	      	  (y : IDesc I)
			          (t : UId) => 
				     ((: Set) (P ('piD (Enum ['tt 'ff]) [x y])) == (: Set) (P ('prodD t x y)))))
		   (methodVar : (i : I) -> P ('varD i))
		   (methodConst : (K : Set) -> P ('constD K))
		   (methodPi : (S : Set) -> (T : S -> IDesc I) -> P ('piD S T))
		   (methodSigma : (S : Set) -> (T : S -> IDesc I) -> P ('sigmaD S T)) : P x ;

<=  TData.tcase (Sig ()) [ IDescConstructors (\ _ -> IDescBranches I)] [] x ;
= methodVar xf;
= methodConst xf;
= methodPi S T;
= substEq Set (P ('piD (Enum E) T)) (P ('fpiD E T)) (pf-Pi E T) (\ x -> x) (methodPi (Enum E) T); 
--<= substEq Set (P ('piD (Enum E) T)) (P ('fpiD E T)) (Pf-Pi E T) ;
= methodSigma S T;
-- <= substEq (IDesc I) ('sigmaD (Enum s) (\ x -> switch s x (\ _ -> IDesc I) xf)) ('fsigmaD s xf) (pf-Sigma s xf);
= substEq Set (P ('sigmaD (Enum E) (\ x -> switch E x (\ _ -> IDesc I) T))) (P ('fsigmaD E T)) (pf-Sigma E T) (\ x -> x) (methodSigma (Enum E) (\ x -> switch E x (\ _ -> IDesc I) T));
-- <= substEq (IDesc I) ('piD (Enum ['tt 'ff]) [xf^1 xf]) ('prodD xf^1 xf) (pf-Prod xf^1 xf);
= substEq Set (P ('piD (Enum ['tt 'ff]) [C D])) (P ('prodD u C D)) (pf-Prod C D u) (\ x -> x) (methodPi (Enum ['tt 'ff]) [C D]);
root;