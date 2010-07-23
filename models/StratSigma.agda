module StratSigma where

data Sigma0 (A : Set0) (B : A -> Set0) : Set0 where
    _,_ : (x : A) (y : B x) -> Sigma0 A B

_*0_ : (A : Set0)(B : Set0) -> Set0
A *0 B = Sigma0 A \_ -> B

fst0 : {A : Set0}{B : A -> Set0} -> Sigma0 A B -> A
fst0 (a , _) = a

snd0 : {A : Set0}{B : A -> Set0} (p : Sigma0 A B) -> B (fst0 p)
snd0 (a , b) = b

data Zero0 : Set0 where

data Unit0 : Set0 where
    Void : Unit0

data Sigma1 (A : Set1) (B : A -> Set1) : Set1 where
    _,_ : (x : A) (y : B x) -> Sigma1 A B

_*1_ : (A : Set1)(B : Set1) -> Set1
A *1 B = Sigma1 A \_ -> B

fst1 : {A : Set1}{B : A -> Set1} -> Sigma1 A B -> A
fst1 (a , _) = a

snd1 : {A : Set1}{B : A -> Set1} (p : Sigma1 A B) -> B (fst1 p)
snd1 (a , b) = b

data Zero1 : Set1 where

data Unit1 : Set1 where
    Void : Unit1

data Sigma2 (A : Set2) (B : A -> Set2) : Set2 where
    _,_ : (x : A) (y : B x) -> Sigma2 A B

_*2_ : (A : Set2)(B : Set2) -> Set2
A *2 B = Sigma2 A \_ -> B

fst2 : {A : Set2}{B : A -> Set2} -> Sigma2 A B -> A
fst2 (a , _) = a

snd2 : {A : Set2}{B : A -> Set2} (p : Sigma2 A B) -> B (fst2 p)
snd2 (a , b) = b

data Zero2 : Set2 where

data Unit2 : Set2 where
    Void : Unit2

data Sigma3 (A : Set3) (B : A -> Set3) : Set3 where
    _,_ : (x : A) (y : B x) -> Sigma3 A B

_*3_ : (A : Set3)(B : Set3) -> Set3
A *3 B = Sigma3 A \_ -> B

fst3 : {A : Set3}{B : A -> Set3} -> Sigma3 A B -> A
fst3 (a , _) = a

snd3 : {A : Set3}{B : A -> Set3} (p : Sigma3 A B) -> B (fst3 p)
snd3 (a , b) = b

data Zero3 : Set3 where

data Unit3 : Set3 where
    Void : Unit3

data Sigma4 (A : Set4) (B : A -> Set4) : Set4 where
    _,_ : (x : A) (y : B x) -> Sigma4 A B

_*4_ : (A : Set4)(B : Set4) -> Set4
A *4 B = Sigma4 A \_ -> B

fst4 : {A : Set4}{B : A -> Set4} -> Sigma4 A B -> A
fst4 (a , _) = a

snd4 : {A : Set4}{B : A -> Set4} (p : Sigma4 A B) -> B (fst4 p)
snd4 (a , b) = b

data Zero4 : Set4 where

data Unit4 : Set4 where
    Void : Unit4

data Sigma5 (A : Set5) (B : A -> Set5) : Set5 where
    _,_ : (x : A) (y : B x) -> Sigma5 A B

_*5_ : (A : Set5)(B : Set5) -> Set5
A *5 B = Sigma5 A \_ -> B

fst5 : {A : Set5}{B : A -> Set5} -> Sigma5 A B -> A
fst5 (a , _) = a

snd5 : {A : Set5}{B : A -> Set5} (p : Sigma5 A B) -> B (fst5 p)
snd5 (a , b) = b

data Zero5 : Set5 where

data Unit5 : Set5 where
    Void : Unit5

data Sigma6 (A : Set6) (B : A -> Set6) : Set6 where
    _,_ : (x : A) (y : B x) -> Sigma6 A B

_*6_ : (A : Set6)(B : Set6) -> Set6
A *6 B = Sigma6 A \_ -> B

fst6 : {A : Set6}{B : A -> Set6} -> Sigma6 A B -> A
fst6 (a , _) = a

snd6 : {A : Set6}{B : A -> Set6} (p : Sigma6 A B) -> B (fst6 p)
snd6 (a , b) = b

data Zero6 : Set6 where

data Unit6 : Set6 where
    Void : Unit6

data Sigma7 (A : Set7) (B : A -> Set7) : Set7 where
    _,_ : (x : A) (y : B x) -> Sigma7 A B

_*7_ : (A : Set7)(B : Set7) -> Set7
A *7 B = Sigma7 A \_ -> B

fst7 : {A : Set7}{B : A -> Set7} -> Sigma7 A B -> A
fst7 (a , _) = a

snd7 : {A : Set7}{B : A -> Set7} (p : Sigma7 A B) -> B (fst7 p)
snd7 (a , b) = b

data Zero7 : Set7 where

data Unit7 : Set7 where
    Void : Unit7

data Sigma8 (A : Set8) (B : A -> Set8) : Set8 where
    _,_ : (x : A) (y : B x) -> Sigma8 A B

_*8_ : (A : Set8)(B : Set8) -> Set8
A *8 B = Sigma8 A \_ -> B

fst8 : {A : Set8}{B : A -> Set8} -> Sigma8 A B -> A
fst8 (a , _) = a

snd8 : {A : Set8}{B : A -> Set8} (p : Sigma8 A B) -> B (fst8 p)
snd8 (a , b) = b

data Zero8 : Set8 where

data Unit8 : Set8 where
    Void : Unit8

data Sigma9 (A : Set9) (B : A -> Set9) : Set9 where
    _,_ : (x : A) (y : B x) -> Sigma9 A B

_*9_ : (A : Set9)(B : Set9) -> Set9
A *9 B = Sigma9 A \_ -> B

fst9 : {A : Set9}{B : A -> Set9} -> Sigma9 A B -> A
fst9 (a , _) = a

snd9 : {A : Set9}{B : A -> Set9} (p : Sigma9 A B) -> B (fst9 p)
snd9 (a , b) = b

data Zero9 : Set9 where

data Unit9 : Set9 where
    Void : Unit9

data Sigma10 (A : Set10) (B : A -> Set10) : Set10 where
    _,_ : (x : A) (y : B x) -> Sigma10 A B

_*10_ : (A : Set10)(B : Set10) -> Set10
A *10 B = Sigma10 A \_ -> B

fst10 : {A : Set10}{B : A -> Set10} -> Sigma10 A B -> A
fst10 (a , _) = a

snd10 : {A : Set10}{B : A -> Set10} (p : Sigma10 A B) -> B (fst10 p)
snd10 (a , b) = b

data Zero10 : Set10 where

data Unit10 : Set10 where
    Void : Unit10

data Sigma11 (A : Set11) (B : A -> Set11) : Set11 where
    _,_ : (x : A) (y : B x) -> Sigma11 A B

_*11_ : (A : Set11)(B : Set11) -> Set11
A *11 B = Sigma11 A \_ -> B

fst11 : {A : Set11}{B : A -> Set11} -> Sigma11 A B -> A
fst11 (a , _) = a

snd11 : {A : Set11}{B : A -> Set11} (p : Sigma11 A B) -> B (fst11 p)
snd11 (a , b) = b

data Zero11 : Set11 where

data Unit11 : Set11 where
    Void : Unit11

data Sigma12 (A : Set12) (B : A -> Set12) : Set12 where
    _,_ : (x : A) (y : B x) -> Sigma12 A B

_*12_ : (A : Set12)(B : Set12) -> Set12
A *12 B = Sigma12 A \_ -> B

fst12 : {A : Set12}{B : A -> Set12} -> Sigma12 A B -> A
fst12 (a , _) = a

snd12 : {A : Set12}{B : A -> Set12} (p : Sigma12 A B) -> B (fst12 p)
snd12 (a , b) = b

data Zero12 : Set12 where

data Unit12 : Set12 where
    Void : Unit12

data Sigma13 (A : Set13) (B : A -> Set13) : Set13 where
    _,_ : (x : A) (y : B x) -> Sigma13 A B

_*13_ : (A : Set13)(B : Set13) -> Set13
A *13 B = Sigma13 A \_ -> B

fst13 : {A : Set13}{B : A -> Set13} -> Sigma13 A B -> A
fst13 (a , _) = a

snd13 : {A : Set13}{B : A -> Set13} (p : Sigma13 A B) -> B (fst13 p)
snd13 (a , b) = b

data Zero13 : Set13 where

data Unit13 : Set13 where
    Void : Unit13

data Sigma14 (A : Set14) (B : A -> Set14) : Set14 where
    _,_ : (x : A) (y : B x) -> Sigma14 A B

_*14_ : (A : Set14)(B : Set14) -> Set14
A *14 B = Sigma14 A \_ -> B

fst14 : {A : Set14}{B : A -> Set14} -> Sigma14 A B -> A
fst14 (a , _) = a

snd14 : {A : Set14}{B : A -> Set14} (p : Sigma14 A B) -> B (fst14 p)
snd14 (a , b) = b

data Zero14 : Set14 where

data Unit14 : Set14 where
    Void : Unit14

data Sigma15 (A : Set15) (B : A -> Set15) : Set15 where
    _,_ : (x : A) (y : B x) -> Sigma15 A B

_*15_ : (A : Set15)(B : Set15) -> Set15
A *15 B = Sigma15 A \_ -> B

fst15 : {A : Set15}{B : A -> Set15} -> Sigma15 A B -> A
fst15 (a , _) = a

snd15 : {A : Set15}{B : A -> Set15} (p : Sigma15 A B) -> B (fst15 p)
snd15 (a , b) = b

data Zero15 : Set15 where

data Unit15 : Set15 where
    Void : Unit15

data Sigma16 (A : Set16) (B : A -> Set16) : Set16 where
    _,_ : (x : A) (y : B x) -> Sigma16 A B

_*16_ : (A : Set16)(B : Set16) -> Set16
A *16 B = Sigma16 A \_ -> B

fst16 : {A : Set16}{B : A -> Set16} -> Sigma16 A B -> A
fst16 (a , _) = a

snd16 : {A : Set16}{B : A -> Set16} (p : Sigma16 A B) -> B (fst16 p)
snd16 (a , b) = b

data Zero16 : Set16 where

data Unit16 : Set16 where
    Void : Unit16

data Sigma17 (A : Set17) (B : A -> Set17) : Set17 where
    _,_ : (x : A) (y : B x) -> Sigma17 A B

_*17_ : (A : Set17)(B : Set17) -> Set17
A *17 B = Sigma17 A \_ -> B

fst17 : {A : Set17}{B : A -> Set17} -> Sigma17 A B -> A
fst17 (a , _) = a

snd17 : {A : Set17}{B : A -> Set17} (p : Sigma17 A B) -> B (fst17 p)
snd17 (a , b) = b

data Zero17 : Set17 where

data Unit17 : Set17 where
    Void : Unit17

data Sigma18 (A : Set18) (B : A -> Set18) : Set18 where
    _,_ : (x : A) (y : B x) -> Sigma18 A B

_*18_ : (A : Set18)(B : Set18) -> Set18
A *18 B = Sigma18 A \_ -> B

fst18 : {A : Set18}{B : A -> Set18} -> Sigma18 A B -> A
fst18 (a , _) = a

snd18 : {A : Set18}{B : A -> Set18} (p : Sigma18 A B) -> B (fst18 p)
snd18 (a , b) = b

data Zero18 : Set18 where

data Unit18 : Set18 where
    Void : Unit18

data Sigma19 (A : Set19) (B : A -> Set19) : Set19 where
    _,_ : (x : A) (y : B x) -> Sigma19 A B

_*19_ : (A : Set19)(B : Set19) -> Set19
A *19 B = Sigma19 A \_ -> B

fst19 : {A : Set19}{B : A -> Set19} -> Sigma19 A B -> A
fst19 (a , _) = a

snd19 : {A : Set19}{B : A -> Set19} (p : Sigma19 A B) -> B (fst19 p)
snd19 (a , b) = b

data Zero19 : Set19 where

data Unit19 : Set19 where
    Void : Unit19

data Sigma20 (A : Set20) (B : A -> Set20) : Set20 where
    _,_ : (x : A) (y : B x) -> Sigma20 A B

_*20_ : (A : Set20)(B : Set20) -> Set20
A *20 B = Sigma20 A \_ -> B

fst20 : {A : Set20}{B : A -> Set20} -> Sigma20 A B -> A
fst20 (a , _) = a

snd20 : {A : Set20}{B : A -> Set20} (p : Sigma20 A B) -> B (fst20 p)
snd20 (a , b) = b

data Zero20 : Set20 where

data Unit20 : Set20 where
    Void : Unit20

data Sigma21 (A : Set21) (B : A -> Set21) : Set21 where
    _,_ : (x : A) (y : B x) -> Sigma21 A B

_*21_ : (A : Set21)(B : Set21) -> Set21
A *21 B = Sigma21 A \_ -> B

fst21 : {A : Set21}{B : A -> Set21} -> Sigma21 A B -> A
fst21 (a , _) = a

snd21 : {A : Set21}{B : A -> Set21} (p : Sigma21 A B) -> B (fst21 p)
snd21 (a , b) = b

data Zero21 : Set21 where

data Unit21 : Set21 where
    Void : Unit21

data Sigma22 (A : Set22) (B : A -> Set22) : Set22 where
    _,_ : (x : A) (y : B x) -> Sigma22 A B

_*22_ : (A : Set22)(B : Set22) -> Set22
A *22 B = Sigma22 A \_ -> B

fst22 : {A : Set22}{B : A -> Set22} -> Sigma22 A B -> A
fst22 (a , _) = a

snd22 : {A : Set22}{B : A -> Set22} (p : Sigma22 A B) -> B (fst22 p)
snd22 (a , b) = b

data Zero22 : Set22 where

data Unit22 : Set22 where
    Void : Unit22

data Sigma23 (A : Set23) (B : A -> Set23) : Set23 where
    _,_ : (x : A) (y : B x) -> Sigma23 A B

_*23_ : (A : Set23)(B : Set23) -> Set23
A *23 B = Sigma23 A \_ -> B

fst23 : {A : Set23}{B : A -> Set23} -> Sigma23 A B -> A
fst23 (a , _) = a

snd23 : {A : Set23}{B : A -> Set23} (p : Sigma23 A B) -> B (fst23 p)
snd23 (a , b) = b

data Zero23 : Set23 where

data Unit23 : Set23 where
    Void : Unit23

data Sigma24 (A : Set24) (B : A -> Set24) : Set24 where
    _,_ : (x : A) (y : B x) -> Sigma24 A B

_*24_ : (A : Set24)(B : Set24) -> Set24
A *24 B = Sigma24 A \_ -> B

fst24 : {A : Set24}{B : A -> Set24} -> Sigma24 A B -> A
fst24 (a , _) = a

snd24 : {A : Set24}{B : A -> Set24} (p : Sigma24 A B) -> B (fst24 p)
snd24 (a , b) = b

data Zero24 : Set24 where

data Unit24 : Set24 where
    Void : Unit24

data Sigma25 (A : Set25) (B : A -> Set25) : Set25 where
    _,_ : (x : A) (y : B x) -> Sigma25 A B

_*25_ : (A : Set25)(B : Set25) -> Set25
A *25 B = Sigma25 A \_ -> B

fst25 : {A : Set25}{B : A -> Set25} -> Sigma25 A B -> A
fst25 (a , _) = a

snd25 : {A : Set25}{B : A -> Set25} (p : Sigma25 A B) -> B (fst25 p)
snd25 (a , b) = b

data Zero25 : Set25 where

data Unit25 : Set25 where
    Void : Unit25

data Sigma26 (A : Set26) (B : A -> Set26) : Set26 where
    _,_ : (x : A) (y : B x) -> Sigma26 A B

_*26_ : (A : Set26)(B : Set26) -> Set26
A *26 B = Sigma26 A \_ -> B

fst26 : {A : Set26}{B : A -> Set26} -> Sigma26 A B -> A
fst26 (a , _) = a

snd26 : {A : Set26}{B : A -> Set26} (p : Sigma26 A B) -> B (fst26 p)
snd26 (a , b) = b

data Zero26 : Set26 where

data Unit26 : Set26 where
    Void : Unit26

data Sigma27 (A : Set27) (B : A -> Set27) : Set27 where
    _,_ : (x : A) (y : B x) -> Sigma27 A B

_*27_ : (A : Set27)(B : Set27) -> Set27
A *27 B = Sigma27 A \_ -> B

fst27 : {A : Set27}{B : A -> Set27} -> Sigma27 A B -> A
fst27 (a , _) = a

snd27 : {A : Set27}{B : A -> Set27} (p : Sigma27 A B) -> B (fst27 p)
snd27 (a , b) = b

data Zero27 : Set27 where

data Unit27 : Set27 where
    Void : Unit27

data Sigma28 (A : Set28) (B : A -> Set28) : Set28 where
    _,_ : (x : A) (y : B x) -> Sigma28 A B

_*28_ : (A : Set28)(B : Set28) -> Set28
A *28 B = Sigma28 A \_ -> B

fst28 : {A : Set28}{B : A -> Set28} -> Sigma28 A B -> A
fst28 (a , _) = a

snd28 : {A : Set28}{B : A -> Set28} (p : Sigma28 A B) -> B (fst28 p)
snd28 (a , b) = b

data Zero28 : Set28 where

data Unit28 : Set28 where
    Void : Unit28

data Sigma29 (A : Set29) (B : A -> Set29) : Set29 where
    _,_ : (x : A) (y : B x) -> Sigma29 A B

_*29_ : (A : Set29)(B : Set29) -> Set29
A *29 B = Sigma29 A \_ -> B

fst29 : {A : Set29}{B : A -> Set29} -> Sigma29 A B -> A
fst29 (a , _) = a

snd29 : {A : Set29}{B : A -> Set29} (p : Sigma29 A B) -> B (fst29 p)
snd29 (a , b) = b

data Zero29 : Set29 where

data Unit29 : Set29 where
    Void : Unit29

data Sigma30 (A : Set30) (B : A -> Set30) : Set30 where
    _,_ : (x : A) (y : B x) -> Sigma30 A B

_*30_ : (A : Set30)(B : Set30) -> Set30
A *30 B = Sigma30 A \_ -> B

fst30 : {A : Set30}{B : A -> Set30} -> Sigma30 A B -> A
fst30 (a , _) = a

snd30 : {A : Set30}{B : A -> Set30} (p : Sigma30 A B) -> B (fst30 p)
snd30 (a , b) = b

data Zero30 : Set30 where

data Unit30 : Set30 where
    Void : Unit30

data Sigma31 (A : Set31) (B : A -> Set31) : Set31 where
    _,_ : (x : A) (y : B x) -> Sigma31 A B

_*31_ : (A : Set31)(B : Set31) -> Set31
A *31 B = Sigma31 A \_ -> B

fst31 : {A : Set31}{B : A -> Set31} -> Sigma31 A B -> A
fst31 (a , _) = a

snd31 : {A : Set31}{B : A -> Set31} (p : Sigma31 A B) -> B (fst31 p)
snd31 (a , b) = b

data Zero31 : Set31 where

data Unit31 : Set31 where
    Void : Unit31

data Sigma32 (A : Set32) (B : A -> Set32) : Set32 where
    _,_ : (x : A) (y : B x) -> Sigma32 A B

_*32_ : (A : Set32)(B : Set32) -> Set32
A *32 B = Sigma32 A \_ -> B

fst32 : {A : Set32}{B : A -> Set32} -> Sigma32 A B -> A
fst32 (a , _) = a

snd32 : {A : Set32}{B : A -> Set32} (p : Sigma32 A B) -> B (fst32 p)
snd32 (a , b) = b

data Zero32 : Set32 where

data Unit32 : Set32 where
    Void : Unit32

data Sigma33 (A : Set33) (B : A -> Set33) : Set33 where
    _,_ : (x : A) (y : B x) -> Sigma33 A B

_*33_ : (A : Set33)(B : Set33) -> Set33
A *33 B = Sigma33 A \_ -> B

fst33 : {A : Set33}{B : A -> Set33} -> Sigma33 A B -> A
fst33 (a , _) = a

snd33 : {A : Set33}{B : A -> Set33} (p : Sigma33 A B) -> B (fst33 p)
snd33 (a , b) = b

data Zero33 : Set33 where

data Unit33 : Set33 where
    Void : Unit33

data Sigma34 (A : Set34) (B : A -> Set34) : Set34 where
    _,_ : (x : A) (y : B x) -> Sigma34 A B

_*34_ : (A : Set34)(B : Set34) -> Set34
A *34 B = Sigma34 A \_ -> B

fst34 : {A : Set34}{B : A -> Set34} -> Sigma34 A B -> A
fst34 (a , _) = a

snd34 : {A : Set34}{B : A -> Set34} (p : Sigma34 A B) -> B (fst34 p)
snd34 (a , b) = b

data Zero34 : Set34 where

data Unit34 : Set34 where
    Void : Unit34

data Sigma35 (A : Set35) (B : A -> Set35) : Set35 where
    _,_ : (x : A) (y : B x) -> Sigma35 A B

_*35_ : (A : Set35)(B : Set35) -> Set35
A *35 B = Sigma35 A \_ -> B

fst35 : {A : Set35}{B : A -> Set35} -> Sigma35 A B -> A
fst35 (a , _) = a

snd35 : {A : Set35}{B : A -> Set35} (p : Sigma35 A B) -> B (fst35 p)
snd35 (a , b) = b

data Zero35 : Set35 where

data Unit35 : Set35 where
    Void : Unit35

data Sigma36 (A : Set36) (B : A -> Set36) : Set36 where
    _,_ : (x : A) (y : B x) -> Sigma36 A B

_*36_ : (A : Set36)(B : Set36) -> Set36
A *36 B = Sigma36 A \_ -> B

fst36 : {A : Set36}{B : A -> Set36} -> Sigma36 A B -> A
fst36 (a , _) = a

snd36 : {A : Set36}{B : A -> Set36} (p : Sigma36 A B) -> B (fst36 p)
snd36 (a , b) = b

data Zero36 : Set36 where

data Unit36 : Set36 where
    Void : Unit36

data Sigma37 (A : Set37) (B : A -> Set37) : Set37 where
    _,_ : (x : A) (y : B x) -> Sigma37 A B

_*37_ : (A : Set37)(B : Set37) -> Set37
A *37 B = Sigma37 A \_ -> B

fst37 : {A : Set37}{B : A -> Set37} -> Sigma37 A B -> A
fst37 (a , _) = a

snd37 : {A : Set37}{B : A -> Set37} (p : Sigma37 A B) -> B (fst37 p)
snd37 (a , b) = b

data Zero37 : Set37 where

data Unit37 : Set37 where
    Void : Unit37

data Sigma38 (A : Set38) (B : A -> Set38) : Set38 where
    _,_ : (x : A) (y : B x) -> Sigma38 A B

_*38_ : (A : Set38)(B : Set38) -> Set38
A *38 B = Sigma38 A \_ -> B

fst38 : {A : Set38}{B : A -> Set38} -> Sigma38 A B -> A
fst38 (a , _) = a

snd38 : {A : Set38}{B : A -> Set38} (p : Sigma38 A B) -> B (fst38 p)
snd38 (a , b) = b

data Zero38 : Set38 where

data Unit38 : Set38 where
    Void : Unit38

data Sigma39 (A : Set39) (B : A -> Set39) : Set39 where
    _,_ : (x : A) (y : B x) -> Sigma39 A B

_*39_ : (A : Set39)(B : Set39) -> Set39
A *39 B = Sigma39 A \_ -> B

fst39 : {A : Set39}{B : A -> Set39} -> Sigma39 A B -> A
fst39 (a , _) = a

snd39 : {A : Set39}{B : A -> Set39} (p : Sigma39 A B) -> B (fst39 p)
snd39 (a , b) = b

data Zero39 : Set39 where

data Unit39 : Set39 where
    Void : Unit39

data Sigma40 (A : Set40) (B : A -> Set40) : Set40 where
    _,_ : (x : A) (y : B x) -> Sigma40 A B

_*40_ : (A : Set40)(B : Set40) -> Set40
A *40 B = Sigma40 A \_ -> B

fst40 : {A : Set40}{B : A -> Set40} -> Sigma40 A B -> A
fst40 (a , _) = a

snd40 : {A : Set40}{B : A -> Set40} (p : Sigma40 A B) -> B (fst40 p)
snd40 (a , b) = b

data Zero40 : Set40 where

data Unit40 : Set40 where
    Void : Unit40

data Sigma41 (A : Set41) (B : A -> Set41) : Set41 where
    _,_ : (x : A) (y : B x) -> Sigma41 A B

_*41_ : (A : Set41)(B : Set41) -> Set41
A *41 B = Sigma41 A \_ -> B

fst41 : {A : Set41}{B : A -> Set41} -> Sigma41 A B -> A
fst41 (a , _) = a

snd41 : {A : Set41}{B : A -> Set41} (p : Sigma41 A B) -> B (fst41 p)
snd41 (a , b) = b

data Zero41 : Set41 where

data Unit41 : Set41 where
    Void : Unit41

data Sigma42 (A : Set42) (B : A -> Set42) : Set42 where
    _,_ : (x : A) (y : B x) -> Sigma42 A B

_*42_ : (A : Set42)(B : Set42) -> Set42
A *42 B = Sigma42 A \_ -> B

fst42 : {A : Set42}{B : A -> Set42} -> Sigma42 A B -> A
fst42 (a , _) = a

snd42 : {A : Set42}{B : A -> Set42} (p : Sigma42 A B) -> B (fst42 p)
snd42 (a , b) = b

data Zero42 : Set42 where

data Unit42 : Set42 where
    Void : Unit42
