make Bool := (Enum ['true 'false]) : Set ;
make So : Bool -> Set ;
lambda b ;
give IMu Bool (\ b -> IDone (((: Bool) 'true) == b)) b ;
make oh := con [] : So 'true ;
