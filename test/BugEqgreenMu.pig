make Empty1D := Mu (con ['constD (Sig ())]) : Set ;
make Empty2D := Mu (con ['constD (Sig ())]) : Set ;
elab eqGreen Set (Mu (con ['constD (Sig ())])) Set (Mu (con ['constD (Sig ())])) ;
elab eqGreen Set Empty1D Set (Mu (con ['constD (Sig ())])) ;
elab eqGreen Set (Mu (con ['constD (Sig ())])) Set Empty2D  ;
elab eqGreen Set Empty1D Set Empty2D  ;
elab coe (Mu (con ['constD (Sig ())])) (Mu (con ['constD (Sig ())])) _ (con []) ;
