data Nat := ('zero : Nat) ; ('suc : (n : Nat) -> Nat);

let Le (x : Nat)(y : Nat) : Prop;
refine Le x y <= Nat.Ind x ;
refine   Le 'zero y = TT;
refine   Le ('suc x) y <= Nat.Ind y;
refine     Le ('suc x) 'zero    = FF;
refine     Le ('suc x) ('suc y) = Le x y;
root;

let owotoNat (x : Nat)(y : Nat)(P : Set)
             (ple : (:- Le x y) -> P)
             (pge : (:- Le y x) -> P)
             : P ;
refine owotoNat x y P ple pge <= Nat.Ind x;
refine   owotoNat 'zero y P ple pge = ple _;
refine   owotoNat ('suc x) y P ple pge <= Nat.Ind y;
refine     owotoNat ('suc x) 'zero P ple pge = pge _;
refine     owotoNat ('suc x) ('suc y) P ple pge <= owotoNat x y;
refine       owotoNat ('suc x) ('suc y) P ple pge = ple _;
refine       owotoNat ('suc x) ('suc y) P ple pge = pge _;
root;

data BT (X : Set) := ('bot : BT X) ; ('el : X -> BT X) ; ('top : BT X) ;

let BTLe (X : Set)(LE : X -> X -> Prop)(x : BT X)(y : BT X) : Prop ;
refine BTLe X LE x y <= BT.Ind X x ;
refine   BTLe X LE 'bot y = TT ;
refine   BTLe X LE ('el x) y <= BT.Ind X y ;
refine     BTLe X LE ('el x) 'bot = FF ;
refine     BTLe X LE ('el x) ('el y) = LE x y ;
refine     BTLe X LE ('el x) 'top = TT ;
refine   BTLe X LE 'top y <= BT.Ind X y ;
refine     BTLe X LE 'top 'bot = FF ;
refine     BTLe X LE 'top ('el y) = FF ;
refine     BTLe X LE 'top 'top = TT ;
root;

let Bounds : Set ;
refine Bounds = Sig (l : BT Nat ; u : BT Nat ; ) ;
root;

let Bdd (x : Nat)(lu : Bounds) : Prop ;
refine Bdd x [l u] = BTLe Nat Le l ('el x) && BTLe Nat Le ('el x) u ;
root;

let OListD (lu : Bounds) : IDesc Bounds ;
refine OListD [l u] = 'fsigmaD ['nil 'cons] [? ?];
  give 'constD (:- BTLe Nat Le l u) ;
  give 'sigmaD Nat \ x -> 'prodD 'xs ('varD [('el x) u]) ('constD (:- BTLe Nat Le l ('el x))) ;
root;

let OList (lu : Bounds) : Set ;
refine OList [l u] = IMu Bounds OListD [l u] ;
root;

let insert (lu : Bounds)(a : Nat)(as : OList lu)(p : :- Bdd a lu) : OList lu ;
refine insert [l u] a as _ <= iinduction Bounds OListD [l u] as ;
refine   insert [l u] a 'nil _ = 'cons a 'nil ;
refine   insert [l u] a ('cons b bs) _ <= owotoNat a b ;
refine     insert [l u] a ('cons b bs) _ = 'cons a ('cons b bs) ;
refine     insert [l u] a ('cons b bs) _ = 'cons b (insert [('el b) u] a bs _) ;
root;

data List (X : Set) := ('nil : List X) ; ('cons : X -> List X -> List X) ;

let isort (xs : List Nat) : OList ['bot 'top] ;
refine isort xs <= List.Ind Nat xs ;
refine   isort 'nil = 'nil ;
refine   isort ('cons a as) = insert ['bot 'top] a (isort as) _ ;
root;

elab isort ('cons ('suc 'zero) ('cons 'zero ('cons ('suc ('suc ('suc 'zero))) ('cons ('suc ('suc 'zero)) 'nil)))) ;
