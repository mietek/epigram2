make TestD := con ['arg (Enum ['zero 'orez]) [ (con ['done]) (con ['done])] ] : Desc ;
make Test := (Mu TestD) : Set ;
make add : Test -> Test ;
lambda x ;
elim elimOp TestD x ;
ind Test ;
show hyps ;
show state ;
