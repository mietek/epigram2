make nat := (Mu con ['arg (Enum ['zero 'suc]) [ (con ['done]) (con ['ind1 con ['
done]]) ] ] ) : Set ;
make zero := con ['zero] : nat ;
make suc := (\ x -> con ['suc x]) : nat -> nat ;
make one := (suc zero) : nat ;
make two := (suc one) : nat ;
make plus : nat -> nat -> nat