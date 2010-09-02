let idescInduction (I : Set)
		   (x : IDesc I [])
      		   (P : IDesc I [] -> Set)
		   (pf-Pi : (E : EnumU)
	                    (T : Enum E -> IDesc I []) -> 
			        (:- (((: IDesc I []) ('piD (Enum E) T)) == ((: IDesc I []) ('fpiD E T)))))
		   (pf-Sigma : (E : EnumU)
		   	       (T : branches E (\ _ -> IDesc I [])) ->
			           (:- (((: IDesc I []) ('sigmaD (Enum E) (\ x -> switch E x (\ _ -> IDesc I []) T))) == ((: IDesc I []) ('fsigmaD E T)))))
		   (pf-Prod : (x : IDesc I [])
		   	      (y : IDesc I []) -> 
				     (:- ((: IDesc I []) ('piD (Enum ['tt 'ff]) [x y]) == (: IDesc I []) ('prodD x y))))
		   (methodVar : (i : I) -> P ('varD i))
		   (methodConst : (K : Set) -> P ('constD K))
		   (methodPi : (S : Set) -> (T : S -> IDesc I []) -> P ('piD S T))
		   (methodSigma : (S : Set) -> (T : S -> IDesc I []) -> P ('sigmaD S T)) : P x ;

<=  icase (Sig ()) IDescConstructors (\ _ -> IDescBranches I) [] x ;
= methodVar s;
= methodConst s;
= methodPi s xf;
<= substEq (IDesc I []) ('piD (Enum s) xf) ('fpiD s xf) (pf-Pi s xf); 
= methodSigma s xf;
<= substEq (IDesc I []) ('sigmaD (Enum s) (\ x -> switch s x (\ _ -> IDesc I []) xf)) ('fsigmaD s xf) (pf-Sigma s xf);
<= substEq (IDesc I []) ('piD (Enum ['tt 'ff]) [xf^1 xf]) ('prodD xf^1 xf) (pf-Prod xf^1 xf);
