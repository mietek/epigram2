module M ;
make A := _ : Set ;
make p := _ : :- A == (: Set) Set ;
lambda X : Set ;
make B := _ : Set ;
make q := _ : :- B == (: Set) Set ;
make C := _ : Set ;
lambda Y : Set ;
make r := _ : :- C == Y ;
make s := _ : :- C == B ;
show state ; 
-- We should be able to figure out that r is unlikely, but s can be solved.