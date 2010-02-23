make TestD := con ['argf ['zero 'orez] [ (con ['done]) (con ['done])] ] : Desc ;
make Test := (Mu TestD) : Set ;
make add : Test -> Test ;
lambda x ;
elim induction TestD x ;
ind Test ;
show hyps ;
show state ;
