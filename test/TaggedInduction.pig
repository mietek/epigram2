module TData ;
{- 

Induction for Tagged Data Types.

If we know that a data type is 'tagged' (i.e. has a constructor choice first
up) we can generate a better induction principle, which splits on those
constructors.

A Tagged Data Type is given by a set (enumeration) of constructors, and a
bunch of descriptions, which can depend on the index given:

-}

make TData  := \ I -> Sig (e : EnumU ; I -> branches e (\ t -> IDesc I) ;) 
            : Set -> Set ;


{-

Given these things, we can build and IDesc, and a Set for the data type:

-}

make dataD := \ I td i -> con ['fsigmaD , [(td !) (td - ! i)] ] 
           : (I : Set) -> TData I -> I -> IDesc I ;

make dataTy := \ I td i -> IMu I (dataD I td) i 
            : (I : Set) -> TData I -> I -> Set ;

{-

We can now build our induction principle, which takes a tuple of branches
(one for each constructor choice) as it's method. It's definition is a
specially instantiated call to the more generic iinduction:

-}

make tind :=  \ I td i x P p -> 
                iinduction I (dataD I td) i x P 
                  (\ i y h -> 
                     switch (td !) (y !) 
                       (\ t -> ((i : I)
                                (xs : idesc I 
                                        (switch (td !) t 
                                          (\ t -> IDesc I) (td - ! i))      
                                          (\ i -> dataTy I td i))
                                (ihs : idesc (Sig (i : I ; dataTy I td i)) 
                                         (ibox I (switch (td !) t 
                                                  (\ t -> IDesc I) (td - ! i))
                                            (dataTy I td) xs) P)
                                -> P [i , con [t , xs]])) p i (y -) h)
          : (I : Set) (td : TData I) (i : I) (x : dataTy I td i) 
              (P : Sig (i : I ; dataTy I td i) -> Set) 
               (p : branches (td !) 
                      (\ t -> (i : I) ->
                              (xs : idesc I (switch (td !) t (\ t -> IDesc I) 
                                      (td - ! i)) (dataTy I td)) 
                         (ihs : idesc 
                                  (Sig (i : I ; dataTy I td i))
                                  (ibox I (switch (td !) t (\ t -> IDesc I) 
                                             (td - ! i))
                                    (dataTy I td) xs)
                                  P)
                         -> P [ i , con [ t , xs ] ]))
                 -> P [ i , x ] ;


{-

These Tagged Data Types are also the ones on which we can employ case
analysis, so let's also build a gadget for that. This resembles tind, but
with anything mentioning the induction hypotheses having been erased:

-}

make tcase :=  \ I td i x P p -> 
                 iinduction I (dataD I td) i x P 
                   (\ i y _ -> 
                      switch (td !) (y !) 
                        (\ t -> ((i : I)
                                 (xs : idesc I 
                                         (switch (td !) t 
                                           (\ t -> IDesc I) (td - ! i))      
                                           (\ i -> dataTy I td i))
                                 -> P [i , con [t , xs]])) p i (y -))
           : (I : Set) (td : TData I) (i : I) (x : dataTy I td i) 
               (P : Sig (i : I ; dataTy I td i) -> Set) 
                (p : branches (td !) 
                      (\ t -> (i : I) ->
                              (xs : idesc I (switch (td !) t (\ t -> IDesc I)
                                     (td - ! i)) (dataTy I td)) 
                               -> P [ i , con [ t , xs ] ]))
                 -> P [ i , x ] ;

{-

These gadgets get specialised for you you when you build a new data type
using 'idata'. The definitions used are bootstrapped via agundry's 'haskell'
tactic from those above (modulo some inlining an miscellaneous other tweaks.

It would be marvellous if this file could form the basis of some kind of 
prelude - if you have any thoughts on how, then don't hold your tongue (:

-}

root ;
