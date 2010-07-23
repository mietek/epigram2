module DescStrat where

open import StratSigma

data Desc42 : Set43 where
    id42 : Desc42
    const42 : Set42 -> Desc42
    prod42 : Desc42 -> Desc42 -> Desc42
    sigma42 : (S : Set42) -> (S -> Desc42) -> Desc42
    pi42 : (S : Set42) -> (S -> Desc42) -> Desc42

[|_|]42_ : Desc42 -> Set42 -> Set42
[| id42 |]42 Z        = Z
[| const42 X |]42 Z   = X
[| prod42 D D' |]42 Z = [| D |]42 Z *42 [| D' |]42 Z
[| sigma42 S T |]42 Z = Sigma42 S (\s -> [| T s |]42 Z)
[| pi42 S T |]42 Z    = (s : S) -> [| T s |]42 Z

data Mu42 (D : Desc42) : Set42 where
    con : [| D |]42 (Mu42 D) -> Mu42 D

data DescDef41 : Set42 where
    DescId41 : DescDef41
    DescConst41 : DescDef41
    DescProd41 : DescDef41
    DescSigma41 : DescDef41
    DescPi41 : DescDef41

data Lift41 (A : Set41) : Set42 where
    lifter : A -> Lift41 A

unlift41 : {A : Set41} -> Lift41 A -> A
unlift41 (lifter a) = a

descCases41 : DescDef41 -> Desc42
descCases41 DescId41 = const42 Unit42
descCases41 DescConst41 = sigma42 Set41 (\_ -> const42 Unit42)
descCases41 DescProd41 = prod42 id42 (prod42 id42 (const42 Unit42))
descCases41 DescSigma41 = sigma42 Set41 (\S -> prod42 (pi42 (Lift41 S)  (\_ -> id42)) (const42 Unit42))
descCases41 DescPi41 = sigma42 Set41 (\S -> prod42 (pi42 (Lift41 S) (\_ -> id42)) (const42 Unit42))

DescD41 : Desc42
DescD41 = sigma42 DescDef41 descCases41

Desc41 : Set42
Desc41 = Mu42 DescD41

id41 : Desc41
id41 = con (DescId41 , Void)

const41 : Set41 -> Desc41
const41 K = con (DescConst41 , (K , Void))

prod41 : (D D' : Desc41) -> Desc41
prod41 D D' = con (DescProd41 , (D , ( D' , Void )))

sigma41 : (S : Set41)(D : S -> Desc41) -> Desc41
sigma41 S D = con (DescSigma41 , (S , ((\s -> D (unlift41 s)) , Void )))

pi41 : (S : Set41)(D : S -> Desc41) -> Desc41
pi41 S D = con (DescPi41 , (S , ((\s -> D (unlift41 s)) , Void )))

[|_|]41_ : Desc41 -> Set41 -> Set41
[| con (DescId41 , Void) |]41 Z = Z
[| con (DescConst41 , ( S , Void)) |]41 Z = S
[| con (DescProd41 , (D , ( D' , Void ))) |]41 Z = [| D |]41 Z *41 [| D' |]41 Z
[| con (DescSigma41 , (S , (T , Void))) |]41 Z =  Sigma41 S (\s -> [| T (lifter s) |]41 Z )
[| con (DescPi41 , (S , (T , Void))) |]41 Z =  (s : S) -> [| T (lifter s) |]41 Z

data Mu41 (D : Desc41) : Set41 where
    con : [| D |]41 (Mu41 D) -> Mu41 D

data DescDef40 : Set41 where
    DescId40 : DescDef40
    DescConst40 : DescDef40
    DescProd40 : DescDef40
    DescSigma40 : DescDef40
    DescPi40 : DescDef40

data Lift40 (A : Set40) : Set41 where
    lifter : A -> Lift40 A

unlift40 : {A : Set40} -> Lift40 A -> A
unlift40 (lifter a) = a

descCases40 : DescDef40 -> Desc41
descCases40 DescId40 = const41 Unit41
descCases40 DescConst40 = sigma41 Set40 (\_ -> const41 Unit41)
descCases40 DescProd40 = prod41 id41 (prod41 id41 (const41 Unit41))
descCases40 DescSigma40 = sigma41 Set40 (\S -> prod41 (pi41 (Lift40 S)  (\_ -> id41)) (const41 Unit41))
descCases40 DescPi40 = sigma41 Set40 (\S -> prod41 (pi41 (Lift40 S) (\_ -> id41)) (const41 Unit41))

DescD40 : Desc41
DescD40 = sigma41 DescDef40 descCases40

Desc40 : Set41
Desc40 = Mu41 DescD40

id40 : Desc40
id40 = con (DescId40 , Void)

const40 : Set40 -> Desc40
const40 K = con (DescConst40 , (K , Void))

prod40 : (D D' : Desc40) -> Desc40
prod40 D D' = con (DescProd40 , (D , ( D' , Void )))

sigma40 : (S : Set40)(D : S -> Desc40) -> Desc40
sigma40 S D = con (DescSigma40 , (S , ((\s -> D (unlift40 s)) , Void )))

pi40 : (S : Set40)(D : S -> Desc40) -> Desc40
pi40 S D = con (DescPi40 , (S , ((\s -> D (unlift40 s)) , Void )))

[|_|]40_ : Desc40 -> Set40 -> Set40
[| con (DescId40 , Void) |]40 Z = Z
[| con (DescConst40 , ( S , Void)) |]40 Z = S
[| con (DescProd40 , (D , ( D' , Void ))) |]40 Z = [| D |]40 Z *40 [| D' |]40 Z
[| con (DescSigma40 , (S , (T , Void))) |]40 Z =  Sigma40 S (\s -> [| T (lifter s) |]40 Z )
[| con (DescPi40 , (S , (T , Void))) |]40 Z =  (s : S) -> [| T (lifter s) |]40 Z

data Mu40 (D : Desc40) : Set40 where
    con : [| D |]40 (Mu40 D) -> Mu40 D

data DescDef39 : Set40 where
    DescId39 : DescDef39
    DescConst39 : DescDef39
    DescProd39 : DescDef39
    DescSigma39 : DescDef39
    DescPi39 : DescDef39

data Lift39 (A : Set39) : Set40 where
    lifter : A -> Lift39 A

unlift39 : {A : Set39} -> Lift39 A -> A
unlift39 (lifter a) = a

descCases39 : DescDef39 -> Desc40
descCases39 DescId39 = const40 Unit40
descCases39 DescConst39 = sigma40 Set39 (\_ -> const40 Unit40)
descCases39 DescProd39 = prod40 id40 (prod40 id40 (const40 Unit40))
descCases39 DescSigma39 = sigma40 Set39 (\S -> prod40 (pi40 (Lift39 S)  (\_ -> id40)) (const40 Unit40))
descCases39 DescPi39 = sigma40 Set39 (\S -> prod40 (pi40 (Lift39 S) (\_ -> id40)) (const40 Unit40))

DescD39 : Desc40
DescD39 = sigma40 DescDef39 descCases39

Desc39 : Set40
Desc39 = Mu40 DescD39

id39 : Desc39
id39 = con (DescId39 , Void)

const39 : Set39 -> Desc39
const39 K = con (DescConst39 , (K , Void))

prod39 : (D D' : Desc39) -> Desc39
prod39 D D' = con (DescProd39 , (D , ( D' , Void )))

sigma39 : (S : Set39)(D : S -> Desc39) -> Desc39
sigma39 S D = con (DescSigma39 , (S , ((\s -> D (unlift39 s)) , Void )))

pi39 : (S : Set39)(D : S -> Desc39) -> Desc39
pi39 S D = con (DescPi39 , (S , ((\s -> D (unlift39 s)) , Void )))

[|_|]39_ : Desc39 -> Set39 -> Set39
[| con (DescId39 , Void) |]39 Z = Z
[| con (DescConst39 , ( S , Void)) |]39 Z = S
[| con (DescProd39 , (D , ( D' , Void ))) |]39 Z = [| D |]39 Z *39 [| D' |]39 Z
[| con (DescSigma39 , (S , (T , Void))) |]39 Z =  Sigma39 S (\s -> [| T (lifter s) |]39 Z )
[| con (DescPi39 , (S , (T , Void))) |]39 Z =  (s : S) -> [| T (lifter s) |]39 Z

data Mu39 (D : Desc39) : Set39 where
    con : [| D |]39 (Mu39 D) -> Mu39 D

data DescDef38 : Set39 where
    DescId38 : DescDef38
    DescConst38 : DescDef38
    DescProd38 : DescDef38
    DescSigma38 : DescDef38
    DescPi38 : DescDef38

data Lift38 (A : Set38) : Set39 where
    lifter : A -> Lift38 A

unlift38 : {A : Set38} -> Lift38 A -> A
unlift38 (lifter a) = a

descCases38 : DescDef38 -> Desc39
descCases38 DescId38 = const39 Unit39
descCases38 DescConst38 = sigma39 Set38 (\_ -> const39 Unit39)
descCases38 DescProd38 = prod39 id39 (prod39 id39 (const39 Unit39))
descCases38 DescSigma38 = sigma39 Set38 (\S -> prod39 (pi39 (Lift38 S)  (\_ -> id39)) (const39 Unit39))
descCases38 DescPi38 = sigma39 Set38 (\S -> prod39 (pi39 (Lift38 S) (\_ -> id39)) (const39 Unit39))

DescD38 : Desc39
DescD38 = sigma39 DescDef38 descCases38

Desc38 : Set39
Desc38 = Mu39 DescD38

id38 : Desc38
id38 = con (DescId38 , Void)

const38 : Set38 -> Desc38
const38 K = con (DescConst38 , (K , Void))

prod38 : (D D' : Desc38) -> Desc38
prod38 D D' = con (DescProd38 , (D , ( D' , Void )))

sigma38 : (S : Set38)(D : S -> Desc38) -> Desc38
sigma38 S D = con (DescSigma38 , (S , ((\s -> D (unlift38 s)) , Void )))

pi38 : (S : Set38)(D : S -> Desc38) -> Desc38
pi38 S D = con (DescPi38 , (S , ((\s -> D (unlift38 s)) , Void )))

[|_|]38_ : Desc38 -> Set38 -> Set38
[| con (DescId38 , Void) |]38 Z = Z
[| con (DescConst38 , ( S , Void)) |]38 Z = S
[| con (DescProd38 , (D , ( D' , Void ))) |]38 Z = [| D |]38 Z *38 [| D' |]38 Z
[| con (DescSigma38 , (S , (T , Void))) |]38 Z =  Sigma38 S (\s -> [| T (lifter s) |]38 Z )
[| con (DescPi38 , (S , (T , Void))) |]38 Z =  (s : S) -> [| T (lifter s) |]38 Z

data Mu38 (D : Desc38) : Set38 where
    con : [| D |]38 (Mu38 D) -> Mu38 D

data DescDef37 : Set38 where
    DescId37 : DescDef37
    DescConst37 : DescDef37
    DescProd37 : DescDef37
    DescSigma37 : DescDef37
    DescPi37 : DescDef37

data Lift37 (A : Set37) : Set38 where
    lifter : A -> Lift37 A

unlift37 : {A : Set37} -> Lift37 A -> A
unlift37 (lifter a) = a

descCases37 : DescDef37 -> Desc38
descCases37 DescId37 = const38 Unit38
descCases37 DescConst37 = sigma38 Set37 (\_ -> const38 Unit38)
descCases37 DescProd37 = prod38 id38 (prod38 id38 (const38 Unit38))
descCases37 DescSigma37 = sigma38 Set37 (\S -> prod38 (pi38 (Lift37 S)  (\_ -> id38)) (const38 Unit38))
descCases37 DescPi37 = sigma38 Set37 (\S -> prod38 (pi38 (Lift37 S) (\_ -> id38)) (const38 Unit38))

DescD37 : Desc38
DescD37 = sigma38 DescDef37 descCases37

Desc37 : Set38
Desc37 = Mu38 DescD37

id37 : Desc37
id37 = con (DescId37 , Void)

const37 : Set37 -> Desc37
const37 K = con (DescConst37 , (K , Void))

prod37 : (D D' : Desc37) -> Desc37
prod37 D D' = con (DescProd37 , (D , ( D' , Void )))

sigma37 : (S : Set37)(D : S -> Desc37) -> Desc37
sigma37 S D = con (DescSigma37 , (S , ((\s -> D (unlift37 s)) , Void )))

pi37 : (S : Set37)(D : S -> Desc37) -> Desc37
pi37 S D = con (DescPi37 , (S , ((\s -> D (unlift37 s)) , Void )))

[|_|]37_ : Desc37 -> Set37 -> Set37
[| con (DescId37 , Void) |]37 Z = Z
[| con (DescConst37 , ( S , Void)) |]37 Z = S
[| con (DescProd37 , (D , ( D' , Void ))) |]37 Z = [| D |]37 Z *37 [| D' |]37 Z
[| con (DescSigma37 , (S , (T , Void))) |]37 Z =  Sigma37 S (\s -> [| T (lifter s) |]37 Z )
[| con (DescPi37 , (S , (T , Void))) |]37 Z =  (s : S) -> [| T (lifter s) |]37 Z

data Mu37 (D : Desc37) : Set37 where
    con : [| D |]37 (Mu37 D) -> Mu37 D

data DescDef36 : Set37 where
    DescId36 : DescDef36
    DescConst36 : DescDef36
    DescProd36 : DescDef36
    DescSigma36 : DescDef36
    DescPi36 : DescDef36

data Lift36 (A : Set36) : Set37 where
    lifter : A -> Lift36 A

unlift36 : {A : Set36} -> Lift36 A -> A
unlift36 (lifter a) = a

descCases36 : DescDef36 -> Desc37
descCases36 DescId36 = const37 Unit37
descCases36 DescConst36 = sigma37 Set36 (\_ -> const37 Unit37)
descCases36 DescProd36 = prod37 id37 (prod37 id37 (const37 Unit37))
descCases36 DescSigma36 = sigma37 Set36 (\S -> prod37 (pi37 (Lift36 S)  (\_ -> id37)) (const37 Unit37))
descCases36 DescPi36 = sigma37 Set36 (\S -> prod37 (pi37 (Lift36 S) (\_ -> id37)) (const37 Unit37))

DescD36 : Desc37
DescD36 = sigma37 DescDef36 descCases36

Desc36 : Set37
Desc36 = Mu37 DescD36

id36 : Desc36
id36 = con (DescId36 , Void)

const36 : Set36 -> Desc36
const36 K = con (DescConst36 , (K , Void))

prod36 : (D D' : Desc36) -> Desc36
prod36 D D' = con (DescProd36 , (D , ( D' , Void )))

sigma36 : (S : Set36)(D : S -> Desc36) -> Desc36
sigma36 S D = con (DescSigma36 , (S , ((\s -> D (unlift36 s)) , Void )))

pi36 : (S : Set36)(D : S -> Desc36) -> Desc36
pi36 S D = con (DescPi36 , (S , ((\s -> D (unlift36 s)) , Void )))

[|_|]36_ : Desc36 -> Set36 -> Set36
[| con (DescId36 , Void) |]36 Z = Z
[| con (DescConst36 , ( S , Void)) |]36 Z = S
[| con (DescProd36 , (D , ( D' , Void ))) |]36 Z = [| D |]36 Z *36 [| D' |]36 Z
[| con (DescSigma36 , (S , (T , Void))) |]36 Z =  Sigma36 S (\s -> [| T (lifter s) |]36 Z )
[| con (DescPi36 , (S , (T , Void))) |]36 Z =  (s : S) -> [| T (lifter s) |]36 Z

data Mu36 (D : Desc36) : Set36 where
    con : [| D |]36 (Mu36 D) -> Mu36 D

data DescDef35 : Set36 where
    DescId35 : DescDef35
    DescConst35 : DescDef35
    DescProd35 : DescDef35
    DescSigma35 : DescDef35
    DescPi35 : DescDef35

data Lift35 (A : Set35) : Set36 where
    lifter : A -> Lift35 A

unlift35 : {A : Set35} -> Lift35 A -> A
unlift35 (lifter a) = a

descCases35 : DescDef35 -> Desc36
descCases35 DescId35 = const36 Unit36
descCases35 DescConst35 = sigma36 Set35 (\_ -> const36 Unit36)
descCases35 DescProd35 = prod36 id36 (prod36 id36 (const36 Unit36))
descCases35 DescSigma35 = sigma36 Set35 (\S -> prod36 (pi36 (Lift35 S)  (\_ -> id36)) (const36 Unit36))
descCases35 DescPi35 = sigma36 Set35 (\S -> prod36 (pi36 (Lift35 S) (\_ -> id36)) (const36 Unit36))

DescD35 : Desc36
DescD35 = sigma36 DescDef35 descCases35

Desc35 : Set36
Desc35 = Mu36 DescD35

id35 : Desc35
id35 = con (DescId35 , Void)

const35 : Set35 -> Desc35
const35 K = con (DescConst35 , (K , Void))

prod35 : (D D' : Desc35) -> Desc35
prod35 D D' = con (DescProd35 , (D , ( D' , Void )))

sigma35 : (S : Set35)(D : S -> Desc35) -> Desc35
sigma35 S D = con (DescSigma35 , (S , ((\s -> D (unlift35 s)) , Void )))

pi35 : (S : Set35)(D : S -> Desc35) -> Desc35
pi35 S D = con (DescPi35 , (S , ((\s -> D (unlift35 s)) , Void )))

[|_|]35_ : Desc35 -> Set35 -> Set35
[| con (DescId35 , Void) |]35 Z = Z
[| con (DescConst35 , ( S , Void)) |]35 Z = S
[| con (DescProd35 , (D , ( D' , Void ))) |]35 Z = [| D |]35 Z *35 [| D' |]35 Z
[| con (DescSigma35 , (S , (T , Void))) |]35 Z =  Sigma35 S (\s -> [| T (lifter s) |]35 Z )
[| con (DescPi35 , (S , (T , Void))) |]35 Z =  (s : S) -> [| T (lifter s) |]35 Z

data Mu35 (D : Desc35) : Set35 where
    con : [| D |]35 (Mu35 D) -> Mu35 D

data DescDef34 : Set35 where
    DescId34 : DescDef34
    DescConst34 : DescDef34
    DescProd34 : DescDef34
    DescSigma34 : DescDef34
    DescPi34 : DescDef34

data Lift34 (A : Set34) : Set35 where
    lifter : A -> Lift34 A

unlift34 : {A : Set34} -> Lift34 A -> A
unlift34 (lifter a) = a

descCases34 : DescDef34 -> Desc35
descCases34 DescId34 = const35 Unit35
descCases34 DescConst34 = sigma35 Set34 (\_ -> const35 Unit35)
descCases34 DescProd34 = prod35 id35 (prod35 id35 (const35 Unit35))
descCases34 DescSigma34 = sigma35 Set34 (\S -> prod35 (pi35 (Lift34 S)  (\_ -> id35)) (const35 Unit35))
descCases34 DescPi34 = sigma35 Set34 (\S -> prod35 (pi35 (Lift34 S) (\_ -> id35)) (const35 Unit35))

DescD34 : Desc35
DescD34 = sigma35 DescDef34 descCases34

Desc34 : Set35
Desc34 = Mu35 DescD34

id34 : Desc34
id34 = con (DescId34 , Void)

const34 : Set34 -> Desc34
const34 K = con (DescConst34 , (K , Void))

prod34 : (D D' : Desc34) -> Desc34
prod34 D D' = con (DescProd34 , (D , ( D' , Void )))

sigma34 : (S : Set34)(D : S -> Desc34) -> Desc34
sigma34 S D = con (DescSigma34 , (S , ((\s -> D (unlift34 s)) , Void )))

pi34 : (S : Set34)(D : S -> Desc34) -> Desc34
pi34 S D = con (DescPi34 , (S , ((\s -> D (unlift34 s)) , Void )))

[|_|]34_ : Desc34 -> Set34 -> Set34
[| con (DescId34 , Void) |]34 Z = Z
[| con (DescConst34 , ( S , Void)) |]34 Z = S
[| con (DescProd34 , (D , ( D' , Void ))) |]34 Z = [| D |]34 Z *34 [| D' |]34 Z
[| con (DescSigma34 , (S , (T , Void))) |]34 Z =  Sigma34 S (\s -> [| T (lifter s) |]34 Z )
[| con (DescPi34 , (S , (T , Void))) |]34 Z =  (s : S) -> [| T (lifter s) |]34 Z

data Mu34 (D : Desc34) : Set34 where
    con : [| D |]34 (Mu34 D) -> Mu34 D

data DescDef33 : Set34 where
    DescId33 : DescDef33
    DescConst33 : DescDef33
    DescProd33 : DescDef33
    DescSigma33 : DescDef33
    DescPi33 : DescDef33

data Lift33 (A : Set33) : Set34 where
    lifter : A -> Lift33 A

unlift33 : {A : Set33} -> Lift33 A -> A
unlift33 (lifter a) = a

descCases33 : DescDef33 -> Desc34
descCases33 DescId33 = const34 Unit34
descCases33 DescConst33 = sigma34 Set33 (\_ -> const34 Unit34)
descCases33 DescProd33 = prod34 id34 (prod34 id34 (const34 Unit34))
descCases33 DescSigma33 = sigma34 Set33 (\S -> prod34 (pi34 (Lift33 S)  (\_ -> id34)) (const34 Unit34))
descCases33 DescPi33 = sigma34 Set33 (\S -> prod34 (pi34 (Lift33 S) (\_ -> id34)) (const34 Unit34))

DescD33 : Desc34
DescD33 = sigma34 DescDef33 descCases33

Desc33 : Set34
Desc33 = Mu34 DescD33

id33 : Desc33
id33 = con (DescId33 , Void)

const33 : Set33 -> Desc33
const33 K = con (DescConst33 , (K , Void))

prod33 : (D D' : Desc33) -> Desc33
prod33 D D' = con (DescProd33 , (D , ( D' , Void )))

sigma33 : (S : Set33)(D : S -> Desc33) -> Desc33
sigma33 S D = con (DescSigma33 , (S , ((\s -> D (unlift33 s)) , Void )))

pi33 : (S : Set33)(D : S -> Desc33) -> Desc33
pi33 S D = con (DescPi33 , (S , ((\s -> D (unlift33 s)) , Void )))

[|_|]33_ : Desc33 -> Set33 -> Set33
[| con (DescId33 , Void) |]33 Z = Z
[| con (DescConst33 , ( S , Void)) |]33 Z = S
[| con (DescProd33 , (D , ( D' , Void ))) |]33 Z = [| D |]33 Z *33 [| D' |]33 Z
[| con (DescSigma33 , (S , (T , Void))) |]33 Z =  Sigma33 S (\s -> [| T (lifter s) |]33 Z )
[| con (DescPi33 , (S , (T , Void))) |]33 Z =  (s : S) -> [| T (lifter s) |]33 Z

data Mu33 (D : Desc33) : Set33 where
    con : [| D |]33 (Mu33 D) -> Mu33 D

data DescDef32 : Set33 where
    DescId32 : DescDef32
    DescConst32 : DescDef32
    DescProd32 : DescDef32
    DescSigma32 : DescDef32
    DescPi32 : DescDef32

data Lift32 (A : Set32) : Set33 where
    lifter : A -> Lift32 A

unlift32 : {A : Set32} -> Lift32 A -> A
unlift32 (lifter a) = a

descCases32 : DescDef32 -> Desc33
descCases32 DescId32 = const33 Unit33
descCases32 DescConst32 = sigma33 Set32 (\_ -> const33 Unit33)
descCases32 DescProd32 = prod33 id33 (prod33 id33 (const33 Unit33))
descCases32 DescSigma32 = sigma33 Set32 (\S -> prod33 (pi33 (Lift32 S)  (\_ -> id33)) (const33 Unit33))
descCases32 DescPi32 = sigma33 Set32 (\S -> prod33 (pi33 (Lift32 S) (\_ -> id33)) (const33 Unit33))

DescD32 : Desc33
DescD32 = sigma33 DescDef32 descCases32

Desc32 : Set33
Desc32 = Mu33 DescD32

id32 : Desc32
id32 = con (DescId32 , Void)

const32 : Set32 -> Desc32
const32 K = con (DescConst32 , (K , Void))

prod32 : (D D' : Desc32) -> Desc32
prod32 D D' = con (DescProd32 , (D , ( D' , Void )))

sigma32 : (S : Set32)(D : S -> Desc32) -> Desc32
sigma32 S D = con (DescSigma32 , (S , ((\s -> D (unlift32 s)) , Void )))

pi32 : (S : Set32)(D : S -> Desc32) -> Desc32
pi32 S D = con (DescPi32 , (S , ((\s -> D (unlift32 s)) , Void )))

[|_|]32_ : Desc32 -> Set32 -> Set32
[| con (DescId32 , Void) |]32 Z = Z
[| con (DescConst32 , ( S , Void)) |]32 Z = S
[| con (DescProd32 , (D , ( D' , Void ))) |]32 Z = [| D |]32 Z *32 [| D' |]32 Z
[| con (DescSigma32 , (S , (T , Void))) |]32 Z =  Sigma32 S (\s -> [| T (lifter s) |]32 Z )
[| con (DescPi32 , (S , (T , Void))) |]32 Z =  (s : S) -> [| T (lifter s) |]32 Z

data Mu32 (D : Desc32) : Set32 where
    con : [| D |]32 (Mu32 D) -> Mu32 D

data DescDef31 : Set32 where
    DescId31 : DescDef31
    DescConst31 : DescDef31
    DescProd31 : DescDef31
    DescSigma31 : DescDef31
    DescPi31 : DescDef31

data Lift31 (A : Set31) : Set32 where
    lifter : A -> Lift31 A

unlift31 : {A : Set31} -> Lift31 A -> A
unlift31 (lifter a) = a

descCases31 : DescDef31 -> Desc32
descCases31 DescId31 = const32 Unit32
descCases31 DescConst31 = sigma32 Set31 (\_ -> const32 Unit32)
descCases31 DescProd31 = prod32 id32 (prod32 id32 (const32 Unit32))
descCases31 DescSigma31 = sigma32 Set31 (\S -> prod32 (pi32 (Lift31 S)  (\_ -> id32)) (const32 Unit32))
descCases31 DescPi31 = sigma32 Set31 (\S -> prod32 (pi32 (Lift31 S) (\_ -> id32)) (const32 Unit32))

DescD31 : Desc32
DescD31 = sigma32 DescDef31 descCases31

Desc31 : Set32
Desc31 = Mu32 DescD31

id31 : Desc31
id31 = con (DescId31 , Void)

const31 : Set31 -> Desc31
const31 K = con (DescConst31 , (K , Void))

prod31 : (D D' : Desc31) -> Desc31
prod31 D D' = con (DescProd31 , (D , ( D' , Void )))

sigma31 : (S : Set31)(D : S -> Desc31) -> Desc31
sigma31 S D = con (DescSigma31 , (S , ((\s -> D (unlift31 s)) , Void )))

pi31 : (S : Set31)(D : S -> Desc31) -> Desc31
pi31 S D = con (DescPi31 , (S , ((\s -> D (unlift31 s)) , Void )))

[|_|]31_ : Desc31 -> Set31 -> Set31
[| con (DescId31 , Void) |]31 Z = Z
[| con (DescConst31 , ( S , Void)) |]31 Z = S
[| con (DescProd31 , (D , ( D' , Void ))) |]31 Z = [| D |]31 Z *31 [| D' |]31 Z
[| con (DescSigma31 , (S , (T , Void))) |]31 Z =  Sigma31 S (\s -> [| T (lifter s) |]31 Z )
[| con (DescPi31 , (S , (T , Void))) |]31 Z =  (s : S) -> [| T (lifter s) |]31 Z

data Mu31 (D : Desc31) : Set31 where
    con : [| D |]31 (Mu31 D) -> Mu31 D

data DescDef30 : Set31 where
    DescId30 : DescDef30
    DescConst30 : DescDef30
    DescProd30 : DescDef30
    DescSigma30 : DescDef30
    DescPi30 : DescDef30

data Lift30 (A : Set30) : Set31 where
    lifter : A -> Lift30 A

unlift30 : {A : Set30} -> Lift30 A -> A
unlift30 (lifter a) = a

descCases30 : DescDef30 -> Desc31
descCases30 DescId30 = const31 Unit31
descCases30 DescConst30 = sigma31 Set30 (\_ -> const31 Unit31)
descCases30 DescProd30 = prod31 id31 (prod31 id31 (const31 Unit31))
descCases30 DescSigma30 = sigma31 Set30 (\S -> prod31 (pi31 (Lift30 S)  (\_ -> id31)) (const31 Unit31))
descCases30 DescPi30 = sigma31 Set30 (\S -> prod31 (pi31 (Lift30 S) (\_ -> id31)) (const31 Unit31))

DescD30 : Desc31
DescD30 = sigma31 DescDef30 descCases30

Desc30 : Set31
Desc30 = Mu31 DescD30

id30 : Desc30
id30 = con (DescId30 , Void)

const30 : Set30 -> Desc30
const30 K = con (DescConst30 , (K , Void))

prod30 : (D D' : Desc30) -> Desc30
prod30 D D' = con (DescProd30 , (D , ( D' , Void )))

sigma30 : (S : Set30)(D : S -> Desc30) -> Desc30
sigma30 S D = con (DescSigma30 , (S , ((\s -> D (unlift30 s)) , Void )))

pi30 : (S : Set30)(D : S -> Desc30) -> Desc30
pi30 S D = con (DescPi30 , (S , ((\s -> D (unlift30 s)) , Void )))

[|_|]30_ : Desc30 -> Set30 -> Set30
[| con (DescId30 , Void) |]30 Z = Z
[| con (DescConst30 , ( S , Void)) |]30 Z = S
[| con (DescProd30 , (D , ( D' , Void ))) |]30 Z = [| D |]30 Z *30 [| D' |]30 Z
[| con (DescSigma30 , (S , (T , Void))) |]30 Z =  Sigma30 S (\s -> [| T (lifter s) |]30 Z )
[| con (DescPi30 , (S , (T , Void))) |]30 Z =  (s : S) -> [| T (lifter s) |]30 Z

data Mu30 (D : Desc30) : Set30 where
    con : [| D |]30 (Mu30 D) -> Mu30 D

data DescDef29 : Set30 where
    DescId29 : DescDef29
    DescConst29 : DescDef29
    DescProd29 : DescDef29
    DescSigma29 : DescDef29
    DescPi29 : DescDef29

data Lift29 (A : Set29) : Set30 where
    lifter : A -> Lift29 A

unlift29 : {A : Set29} -> Lift29 A -> A
unlift29 (lifter a) = a

descCases29 : DescDef29 -> Desc30
descCases29 DescId29 = const30 Unit30
descCases29 DescConst29 = sigma30 Set29 (\_ -> const30 Unit30)
descCases29 DescProd29 = prod30 id30 (prod30 id30 (const30 Unit30))
descCases29 DescSigma29 = sigma30 Set29 (\S -> prod30 (pi30 (Lift29 S)  (\_ -> id30)) (const30 Unit30))
descCases29 DescPi29 = sigma30 Set29 (\S -> prod30 (pi30 (Lift29 S) (\_ -> id30)) (const30 Unit30))

DescD29 : Desc30
DescD29 = sigma30 DescDef29 descCases29

Desc29 : Set30
Desc29 = Mu30 DescD29

id29 : Desc29
id29 = con (DescId29 , Void)

const29 : Set29 -> Desc29
const29 K = con (DescConst29 , (K , Void))

prod29 : (D D' : Desc29) -> Desc29
prod29 D D' = con (DescProd29 , (D , ( D' , Void )))

sigma29 : (S : Set29)(D : S -> Desc29) -> Desc29
sigma29 S D = con (DescSigma29 , (S , ((\s -> D (unlift29 s)) , Void )))

pi29 : (S : Set29)(D : S -> Desc29) -> Desc29
pi29 S D = con (DescPi29 , (S , ((\s -> D (unlift29 s)) , Void )))

[|_|]29_ : Desc29 -> Set29 -> Set29
[| con (DescId29 , Void) |]29 Z = Z
[| con (DescConst29 , ( S , Void)) |]29 Z = S
[| con (DescProd29 , (D , ( D' , Void ))) |]29 Z = [| D |]29 Z *29 [| D' |]29 Z
[| con (DescSigma29 , (S , (T , Void))) |]29 Z =  Sigma29 S (\s -> [| T (lifter s) |]29 Z )
[| con (DescPi29 , (S , (T , Void))) |]29 Z =  (s : S) -> [| T (lifter s) |]29 Z

data Mu29 (D : Desc29) : Set29 where
    con : [| D |]29 (Mu29 D) -> Mu29 D

data DescDef28 : Set29 where
    DescId28 : DescDef28
    DescConst28 : DescDef28
    DescProd28 : DescDef28
    DescSigma28 : DescDef28
    DescPi28 : DescDef28

data Lift28 (A : Set28) : Set29 where
    lifter : A -> Lift28 A

unlift28 : {A : Set28} -> Lift28 A -> A
unlift28 (lifter a) = a

descCases28 : DescDef28 -> Desc29
descCases28 DescId28 = const29 Unit29
descCases28 DescConst28 = sigma29 Set28 (\_ -> const29 Unit29)
descCases28 DescProd28 = prod29 id29 (prod29 id29 (const29 Unit29))
descCases28 DescSigma28 = sigma29 Set28 (\S -> prod29 (pi29 (Lift28 S)  (\_ -> id29)) (const29 Unit29))
descCases28 DescPi28 = sigma29 Set28 (\S -> prod29 (pi29 (Lift28 S) (\_ -> id29)) (const29 Unit29))

DescD28 : Desc29
DescD28 = sigma29 DescDef28 descCases28

Desc28 : Set29
Desc28 = Mu29 DescD28

id28 : Desc28
id28 = con (DescId28 , Void)

const28 : Set28 -> Desc28
const28 K = con (DescConst28 , (K , Void))

prod28 : (D D' : Desc28) -> Desc28
prod28 D D' = con (DescProd28 , (D , ( D' , Void )))

sigma28 : (S : Set28)(D : S -> Desc28) -> Desc28
sigma28 S D = con (DescSigma28 , (S , ((\s -> D (unlift28 s)) , Void )))

pi28 : (S : Set28)(D : S -> Desc28) -> Desc28
pi28 S D = con (DescPi28 , (S , ((\s -> D (unlift28 s)) , Void )))

[|_|]28_ : Desc28 -> Set28 -> Set28
[| con (DescId28 , Void) |]28 Z = Z
[| con (DescConst28 , ( S , Void)) |]28 Z = S
[| con (DescProd28 , (D , ( D' , Void ))) |]28 Z = [| D |]28 Z *28 [| D' |]28 Z
[| con (DescSigma28 , (S , (T , Void))) |]28 Z =  Sigma28 S (\s -> [| T (lifter s) |]28 Z )
[| con (DescPi28 , (S , (T , Void))) |]28 Z =  (s : S) -> [| T (lifter s) |]28 Z

data Mu28 (D : Desc28) : Set28 where
    con : [| D |]28 (Mu28 D) -> Mu28 D

data DescDef27 : Set28 where
    DescId27 : DescDef27
    DescConst27 : DescDef27
    DescProd27 : DescDef27
    DescSigma27 : DescDef27
    DescPi27 : DescDef27

data Lift27 (A : Set27) : Set28 where
    lifter : A -> Lift27 A

unlift27 : {A : Set27} -> Lift27 A -> A
unlift27 (lifter a) = a

descCases27 : DescDef27 -> Desc28
descCases27 DescId27 = const28 Unit28
descCases27 DescConst27 = sigma28 Set27 (\_ -> const28 Unit28)
descCases27 DescProd27 = prod28 id28 (prod28 id28 (const28 Unit28))
descCases27 DescSigma27 = sigma28 Set27 (\S -> prod28 (pi28 (Lift27 S)  (\_ -> id28)) (const28 Unit28))
descCases27 DescPi27 = sigma28 Set27 (\S -> prod28 (pi28 (Lift27 S) (\_ -> id28)) (const28 Unit28))

DescD27 : Desc28
DescD27 = sigma28 DescDef27 descCases27

Desc27 : Set28
Desc27 = Mu28 DescD27

id27 : Desc27
id27 = con (DescId27 , Void)

const27 : Set27 -> Desc27
const27 K = con (DescConst27 , (K , Void))

prod27 : (D D' : Desc27) -> Desc27
prod27 D D' = con (DescProd27 , (D , ( D' , Void )))

sigma27 : (S : Set27)(D : S -> Desc27) -> Desc27
sigma27 S D = con (DescSigma27 , (S , ((\s -> D (unlift27 s)) , Void )))

pi27 : (S : Set27)(D : S -> Desc27) -> Desc27
pi27 S D = con (DescPi27 , (S , ((\s -> D (unlift27 s)) , Void )))

[|_|]27_ : Desc27 -> Set27 -> Set27
[| con (DescId27 , Void) |]27 Z = Z
[| con (DescConst27 , ( S , Void)) |]27 Z = S
[| con (DescProd27 , (D , ( D' , Void ))) |]27 Z = [| D |]27 Z *27 [| D' |]27 Z
[| con (DescSigma27 , (S , (T , Void))) |]27 Z =  Sigma27 S (\s -> [| T (lifter s) |]27 Z )
[| con (DescPi27 , (S , (T , Void))) |]27 Z =  (s : S) -> [| T (lifter s) |]27 Z

data Mu27 (D : Desc27) : Set27 where
    con : [| D |]27 (Mu27 D) -> Mu27 D

data DescDef26 : Set27 where
    DescId26 : DescDef26
    DescConst26 : DescDef26
    DescProd26 : DescDef26
    DescSigma26 : DescDef26
    DescPi26 : DescDef26

data Lift26 (A : Set26) : Set27 where
    lifter : A -> Lift26 A

unlift26 : {A : Set26} -> Lift26 A -> A
unlift26 (lifter a) = a

descCases26 : DescDef26 -> Desc27
descCases26 DescId26 = const27 Unit27
descCases26 DescConst26 = sigma27 Set26 (\_ -> const27 Unit27)
descCases26 DescProd26 = prod27 id27 (prod27 id27 (const27 Unit27))
descCases26 DescSigma26 = sigma27 Set26 (\S -> prod27 (pi27 (Lift26 S)  (\_ -> id27)) (const27 Unit27))
descCases26 DescPi26 = sigma27 Set26 (\S -> prod27 (pi27 (Lift26 S) (\_ -> id27)) (const27 Unit27))

DescD26 : Desc27
DescD26 = sigma27 DescDef26 descCases26

Desc26 : Set27
Desc26 = Mu27 DescD26

id26 : Desc26
id26 = con (DescId26 , Void)

const26 : Set26 -> Desc26
const26 K = con (DescConst26 , (K , Void))

prod26 : (D D' : Desc26) -> Desc26
prod26 D D' = con (DescProd26 , (D , ( D' , Void )))

sigma26 : (S : Set26)(D : S -> Desc26) -> Desc26
sigma26 S D = con (DescSigma26 , (S , ((\s -> D (unlift26 s)) , Void )))

pi26 : (S : Set26)(D : S -> Desc26) -> Desc26
pi26 S D = con (DescPi26 , (S , ((\s -> D (unlift26 s)) , Void )))

[|_|]26_ : Desc26 -> Set26 -> Set26
[| con (DescId26 , Void) |]26 Z = Z
[| con (DescConst26 , ( S , Void)) |]26 Z = S
[| con (DescProd26 , (D , ( D' , Void ))) |]26 Z = [| D |]26 Z *26 [| D' |]26 Z
[| con (DescSigma26 , (S , (T , Void))) |]26 Z =  Sigma26 S (\s -> [| T (lifter s) |]26 Z )
[| con (DescPi26 , (S , (T , Void))) |]26 Z =  (s : S) -> [| T (lifter s) |]26 Z

data Mu26 (D : Desc26) : Set26 where
    con : [| D |]26 (Mu26 D) -> Mu26 D

data DescDef25 : Set26 where
    DescId25 : DescDef25
    DescConst25 : DescDef25
    DescProd25 : DescDef25
    DescSigma25 : DescDef25
    DescPi25 : DescDef25

data Lift25 (A : Set25) : Set26 where
    lifter : A -> Lift25 A

unlift25 : {A : Set25} -> Lift25 A -> A
unlift25 (lifter a) = a

descCases25 : DescDef25 -> Desc26
descCases25 DescId25 = const26 Unit26
descCases25 DescConst25 = sigma26 Set25 (\_ -> const26 Unit26)
descCases25 DescProd25 = prod26 id26 (prod26 id26 (const26 Unit26))
descCases25 DescSigma25 = sigma26 Set25 (\S -> prod26 (pi26 (Lift25 S)  (\_ -> id26)) (const26 Unit26))
descCases25 DescPi25 = sigma26 Set25 (\S -> prod26 (pi26 (Lift25 S) (\_ -> id26)) (const26 Unit26))

DescD25 : Desc26
DescD25 = sigma26 DescDef25 descCases25

Desc25 : Set26
Desc25 = Mu26 DescD25

id25 : Desc25
id25 = con (DescId25 , Void)

const25 : Set25 -> Desc25
const25 K = con (DescConst25 , (K , Void))

prod25 : (D D' : Desc25) -> Desc25
prod25 D D' = con (DescProd25 , (D , ( D' , Void )))

sigma25 : (S : Set25)(D : S -> Desc25) -> Desc25
sigma25 S D = con (DescSigma25 , (S , ((\s -> D (unlift25 s)) , Void )))

pi25 : (S : Set25)(D : S -> Desc25) -> Desc25
pi25 S D = con (DescPi25 , (S , ((\s -> D (unlift25 s)) , Void )))

[|_|]25_ : Desc25 -> Set25 -> Set25
[| con (DescId25 , Void) |]25 Z = Z
[| con (DescConst25 , ( S , Void)) |]25 Z = S
[| con (DescProd25 , (D , ( D' , Void ))) |]25 Z = [| D |]25 Z *25 [| D' |]25 Z
[| con (DescSigma25 , (S , (T , Void))) |]25 Z =  Sigma25 S (\s -> [| T (lifter s) |]25 Z )
[| con (DescPi25 , (S , (T , Void))) |]25 Z =  (s : S) -> [| T (lifter s) |]25 Z

data Mu25 (D : Desc25) : Set25 where
    con : [| D |]25 (Mu25 D) -> Mu25 D

data DescDef24 : Set25 where
    DescId24 : DescDef24
    DescConst24 : DescDef24
    DescProd24 : DescDef24
    DescSigma24 : DescDef24
    DescPi24 : DescDef24

data Lift24 (A : Set24) : Set25 where
    lifter : A -> Lift24 A

unlift24 : {A : Set24} -> Lift24 A -> A
unlift24 (lifter a) = a

descCases24 : DescDef24 -> Desc25
descCases24 DescId24 = const25 Unit25
descCases24 DescConst24 = sigma25 Set24 (\_ -> const25 Unit25)
descCases24 DescProd24 = prod25 id25 (prod25 id25 (const25 Unit25))
descCases24 DescSigma24 = sigma25 Set24 (\S -> prod25 (pi25 (Lift24 S)  (\_ -> id25)) (const25 Unit25))
descCases24 DescPi24 = sigma25 Set24 (\S -> prod25 (pi25 (Lift24 S) (\_ -> id25)) (const25 Unit25))

DescD24 : Desc25
DescD24 = sigma25 DescDef24 descCases24

Desc24 : Set25
Desc24 = Mu25 DescD24

id24 : Desc24
id24 = con (DescId24 , Void)

const24 : Set24 -> Desc24
const24 K = con (DescConst24 , (K , Void))

prod24 : (D D' : Desc24) -> Desc24
prod24 D D' = con (DescProd24 , (D , ( D' , Void )))

sigma24 : (S : Set24)(D : S -> Desc24) -> Desc24
sigma24 S D = con (DescSigma24 , (S , ((\s -> D (unlift24 s)) , Void )))

pi24 : (S : Set24)(D : S -> Desc24) -> Desc24
pi24 S D = con (DescPi24 , (S , ((\s -> D (unlift24 s)) , Void )))

[|_|]24_ : Desc24 -> Set24 -> Set24
[| con (DescId24 , Void) |]24 Z = Z
[| con (DescConst24 , ( S , Void)) |]24 Z = S
[| con (DescProd24 , (D , ( D' , Void ))) |]24 Z = [| D |]24 Z *24 [| D' |]24 Z
[| con (DescSigma24 , (S , (T , Void))) |]24 Z =  Sigma24 S (\s -> [| T (lifter s) |]24 Z )
[| con (DescPi24 , (S , (T , Void))) |]24 Z =  (s : S) -> [| T (lifter s) |]24 Z

data Mu24 (D : Desc24) : Set24 where
    con : [| D |]24 (Mu24 D) -> Mu24 D

data DescDef23 : Set24 where
    DescId23 : DescDef23
    DescConst23 : DescDef23
    DescProd23 : DescDef23
    DescSigma23 : DescDef23
    DescPi23 : DescDef23

data Lift23 (A : Set23) : Set24 where
    lifter : A -> Lift23 A

unlift23 : {A : Set23} -> Lift23 A -> A
unlift23 (lifter a) = a

descCases23 : DescDef23 -> Desc24
descCases23 DescId23 = const24 Unit24
descCases23 DescConst23 = sigma24 Set23 (\_ -> const24 Unit24)
descCases23 DescProd23 = prod24 id24 (prod24 id24 (const24 Unit24))
descCases23 DescSigma23 = sigma24 Set23 (\S -> prod24 (pi24 (Lift23 S)  (\_ -> id24)) (const24 Unit24))
descCases23 DescPi23 = sigma24 Set23 (\S -> prod24 (pi24 (Lift23 S) (\_ -> id24)) (const24 Unit24))

DescD23 : Desc24
DescD23 = sigma24 DescDef23 descCases23

Desc23 : Set24
Desc23 = Mu24 DescD23

id23 : Desc23
id23 = con (DescId23 , Void)

const23 : Set23 -> Desc23
const23 K = con (DescConst23 , (K , Void))

prod23 : (D D' : Desc23) -> Desc23
prod23 D D' = con (DescProd23 , (D , ( D' , Void )))

sigma23 : (S : Set23)(D : S -> Desc23) -> Desc23
sigma23 S D = con (DescSigma23 , (S , ((\s -> D (unlift23 s)) , Void )))

pi23 : (S : Set23)(D : S -> Desc23) -> Desc23
pi23 S D = con (DescPi23 , (S , ((\s -> D (unlift23 s)) , Void )))

[|_|]23_ : Desc23 -> Set23 -> Set23
[| con (DescId23 , Void) |]23 Z = Z
[| con (DescConst23 , ( S , Void)) |]23 Z = S
[| con (DescProd23 , (D , ( D' , Void ))) |]23 Z = [| D |]23 Z *23 [| D' |]23 Z
[| con (DescSigma23 , (S , (T , Void))) |]23 Z =  Sigma23 S (\s -> [| T (lifter s) |]23 Z )
[| con (DescPi23 , (S , (T , Void))) |]23 Z =  (s : S) -> [| T (lifter s) |]23 Z

data Mu23 (D : Desc23) : Set23 where
    con : [| D |]23 (Mu23 D) -> Mu23 D

data DescDef22 : Set23 where
    DescId22 : DescDef22
    DescConst22 : DescDef22
    DescProd22 : DescDef22
    DescSigma22 : DescDef22
    DescPi22 : DescDef22

data Lift22 (A : Set22) : Set23 where
    lifter : A -> Lift22 A

unlift22 : {A : Set22} -> Lift22 A -> A
unlift22 (lifter a) = a

descCases22 : DescDef22 -> Desc23
descCases22 DescId22 = const23 Unit23
descCases22 DescConst22 = sigma23 Set22 (\_ -> const23 Unit23)
descCases22 DescProd22 = prod23 id23 (prod23 id23 (const23 Unit23))
descCases22 DescSigma22 = sigma23 Set22 (\S -> prod23 (pi23 (Lift22 S)  (\_ -> id23)) (const23 Unit23))
descCases22 DescPi22 = sigma23 Set22 (\S -> prod23 (pi23 (Lift22 S) (\_ -> id23)) (const23 Unit23))

DescD22 : Desc23
DescD22 = sigma23 DescDef22 descCases22

Desc22 : Set23
Desc22 = Mu23 DescD22

id22 : Desc22
id22 = con (DescId22 , Void)

const22 : Set22 -> Desc22
const22 K = con (DescConst22 , (K , Void))

prod22 : (D D' : Desc22) -> Desc22
prod22 D D' = con (DescProd22 , (D , ( D' , Void )))

sigma22 : (S : Set22)(D : S -> Desc22) -> Desc22
sigma22 S D = con (DescSigma22 , (S , ((\s -> D (unlift22 s)) , Void )))

pi22 : (S : Set22)(D : S -> Desc22) -> Desc22
pi22 S D = con (DescPi22 , (S , ((\s -> D (unlift22 s)) , Void )))

[|_|]22_ : Desc22 -> Set22 -> Set22
[| con (DescId22 , Void) |]22 Z = Z
[| con (DescConst22 , ( S , Void)) |]22 Z = S
[| con (DescProd22 , (D , ( D' , Void ))) |]22 Z = [| D |]22 Z *22 [| D' |]22 Z
[| con (DescSigma22 , (S , (T , Void))) |]22 Z =  Sigma22 S (\s -> [| T (lifter s) |]22 Z )
[| con (DescPi22 , (S , (T , Void))) |]22 Z =  (s : S) -> [| T (lifter s) |]22 Z

data Mu22 (D : Desc22) : Set22 where
    con : [| D |]22 (Mu22 D) -> Mu22 D

data DescDef21 : Set22 where
    DescId21 : DescDef21
    DescConst21 : DescDef21
    DescProd21 : DescDef21
    DescSigma21 : DescDef21
    DescPi21 : DescDef21

data Lift21 (A : Set21) : Set22 where
    lifter : A -> Lift21 A

unlift21 : {A : Set21} -> Lift21 A -> A
unlift21 (lifter a) = a

descCases21 : DescDef21 -> Desc22
descCases21 DescId21 = const22 Unit22
descCases21 DescConst21 = sigma22 Set21 (\_ -> const22 Unit22)
descCases21 DescProd21 = prod22 id22 (prod22 id22 (const22 Unit22))
descCases21 DescSigma21 = sigma22 Set21 (\S -> prod22 (pi22 (Lift21 S)  (\_ -> id22)) (const22 Unit22))
descCases21 DescPi21 = sigma22 Set21 (\S -> prod22 (pi22 (Lift21 S) (\_ -> id22)) (const22 Unit22))

DescD21 : Desc22
DescD21 = sigma22 DescDef21 descCases21

Desc21 : Set22
Desc21 = Mu22 DescD21

id21 : Desc21
id21 = con (DescId21 , Void)

const21 : Set21 -> Desc21
const21 K = con (DescConst21 , (K , Void))

prod21 : (D D' : Desc21) -> Desc21
prod21 D D' = con (DescProd21 , (D , ( D' , Void )))

sigma21 : (S : Set21)(D : S -> Desc21) -> Desc21
sigma21 S D = con (DescSigma21 , (S , ((\s -> D (unlift21 s)) , Void )))

pi21 : (S : Set21)(D : S -> Desc21) -> Desc21
pi21 S D = con (DescPi21 , (S , ((\s -> D (unlift21 s)) , Void )))

[|_|]21_ : Desc21 -> Set21 -> Set21
[| con (DescId21 , Void) |]21 Z = Z
[| con (DescConst21 , ( S , Void)) |]21 Z = S
[| con (DescProd21 , (D , ( D' , Void ))) |]21 Z = [| D |]21 Z *21 [| D' |]21 Z
[| con (DescSigma21 , (S , (T , Void))) |]21 Z =  Sigma21 S (\s -> [| T (lifter s) |]21 Z )
[| con (DescPi21 , (S , (T , Void))) |]21 Z =  (s : S) -> [| T (lifter s) |]21 Z

data Mu21 (D : Desc21) : Set21 where
    con : [| D |]21 (Mu21 D) -> Mu21 D

data DescDef20 : Set21 where
    DescId20 : DescDef20
    DescConst20 : DescDef20
    DescProd20 : DescDef20
    DescSigma20 : DescDef20
    DescPi20 : DescDef20

data Lift20 (A : Set20) : Set21 where
    lifter : A -> Lift20 A

unlift20 : {A : Set20} -> Lift20 A -> A
unlift20 (lifter a) = a

descCases20 : DescDef20 -> Desc21
descCases20 DescId20 = const21 Unit21
descCases20 DescConst20 = sigma21 Set20 (\_ -> const21 Unit21)
descCases20 DescProd20 = prod21 id21 (prod21 id21 (const21 Unit21))
descCases20 DescSigma20 = sigma21 Set20 (\S -> prod21 (pi21 (Lift20 S)  (\_ -> id21)) (const21 Unit21))
descCases20 DescPi20 = sigma21 Set20 (\S -> prod21 (pi21 (Lift20 S) (\_ -> id21)) (const21 Unit21))

DescD20 : Desc21
DescD20 = sigma21 DescDef20 descCases20

Desc20 : Set21
Desc20 = Mu21 DescD20

id20 : Desc20
id20 = con (DescId20 , Void)

const20 : Set20 -> Desc20
const20 K = con (DescConst20 , (K , Void))

prod20 : (D D' : Desc20) -> Desc20
prod20 D D' = con (DescProd20 , (D , ( D' , Void )))

sigma20 : (S : Set20)(D : S -> Desc20) -> Desc20
sigma20 S D = con (DescSigma20 , (S , ((\s -> D (unlift20 s)) , Void )))

pi20 : (S : Set20)(D : S -> Desc20) -> Desc20
pi20 S D = con (DescPi20 , (S , ((\s -> D (unlift20 s)) , Void )))

[|_|]20_ : Desc20 -> Set20 -> Set20
[| con (DescId20 , Void) |]20 Z = Z
[| con (DescConst20 , ( S , Void)) |]20 Z = S
[| con (DescProd20 , (D , ( D' , Void ))) |]20 Z = [| D |]20 Z *20 [| D' |]20 Z
[| con (DescSigma20 , (S , (T , Void))) |]20 Z =  Sigma20 S (\s -> [| T (lifter s) |]20 Z )
[| con (DescPi20 , (S , (T , Void))) |]20 Z =  (s : S) -> [| T (lifter s) |]20 Z

data Mu20 (D : Desc20) : Set20 where
    con : [| D |]20 (Mu20 D) -> Mu20 D

data DescDef19 : Set20 where
    DescId19 : DescDef19
    DescConst19 : DescDef19
    DescProd19 : DescDef19
    DescSigma19 : DescDef19
    DescPi19 : DescDef19

data Lift19 (A : Set19) : Set20 where
    lifter : A -> Lift19 A

unlift19 : {A : Set19} -> Lift19 A -> A
unlift19 (lifter a) = a

descCases19 : DescDef19 -> Desc20
descCases19 DescId19 = const20 Unit20
descCases19 DescConst19 = sigma20 Set19 (\_ -> const20 Unit20)
descCases19 DescProd19 = prod20 id20 (prod20 id20 (const20 Unit20))
descCases19 DescSigma19 = sigma20 Set19 (\S -> prod20 (pi20 (Lift19 S)  (\_ -> id20)) (const20 Unit20))
descCases19 DescPi19 = sigma20 Set19 (\S -> prod20 (pi20 (Lift19 S) (\_ -> id20)) (const20 Unit20))

DescD19 : Desc20
DescD19 = sigma20 DescDef19 descCases19

Desc19 : Set20
Desc19 = Mu20 DescD19

id19 : Desc19
id19 = con (DescId19 , Void)

const19 : Set19 -> Desc19
const19 K = con (DescConst19 , (K , Void))

prod19 : (D D' : Desc19) -> Desc19
prod19 D D' = con (DescProd19 , (D , ( D' , Void )))

sigma19 : (S : Set19)(D : S -> Desc19) -> Desc19
sigma19 S D = con (DescSigma19 , (S , ((\s -> D (unlift19 s)) , Void )))

pi19 : (S : Set19)(D : S -> Desc19) -> Desc19
pi19 S D = con (DescPi19 , (S , ((\s -> D (unlift19 s)) , Void )))

[|_|]19_ : Desc19 -> Set19 -> Set19
[| con (DescId19 , Void) |]19 Z = Z
[| con (DescConst19 , ( S , Void)) |]19 Z = S
[| con (DescProd19 , (D , ( D' , Void ))) |]19 Z = [| D |]19 Z *19 [| D' |]19 Z
[| con (DescSigma19 , (S , (T , Void))) |]19 Z =  Sigma19 S (\s -> [| T (lifter s) |]19 Z )
[| con (DescPi19 , (S , (T , Void))) |]19 Z =  (s : S) -> [| T (lifter s) |]19 Z

data Mu19 (D : Desc19) : Set19 where
    con : [| D |]19 (Mu19 D) -> Mu19 D

data DescDef18 : Set19 where
    DescId18 : DescDef18
    DescConst18 : DescDef18
    DescProd18 : DescDef18
    DescSigma18 : DescDef18
    DescPi18 : DescDef18

data Lift18 (A : Set18) : Set19 where
    lifter : A -> Lift18 A

unlift18 : {A : Set18} -> Lift18 A -> A
unlift18 (lifter a) = a

descCases18 : DescDef18 -> Desc19
descCases18 DescId18 = const19 Unit19
descCases18 DescConst18 = sigma19 Set18 (\_ -> const19 Unit19)
descCases18 DescProd18 = prod19 id19 (prod19 id19 (const19 Unit19))
descCases18 DescSigma18 = sigma19 Set18 (\S -> prod19 (pi19 (Lift18 S)  (\_ -> id19)) (const19 Unit19))
descCases18 DescPi18 = sigma19 Set18 (\S -> prod19 (pi19 (Lift18 S) (\_ -> id19)) (const19 Unit19))

DescD18 : Desc19
DescD18 = sigma19 DescDef18 descCases18

Desc18 : Set19
Desc18 = Mu19 DescD18

id18 : Desc18
id18 = con (DescId18 , Void)

const18 : Set18 -> Desc18
const18 K = con (DescConst18 , (K , Void))

prod18 : (D D' : Desc18) -> Desc18
prod18 D D' = con (DescProd18 , (D , ( D' , Void )))

sigma18 : (S : Set18)(D : S -> Desc18) -> Desc18
sigma18 S D = con (DescSigma18 , (S , ((\s -> D (unlift18 s)) , Void )))

pi18 : (S : Set18)(D : S -> Desc18) -> Desc18
pi18 S D = con (DescPi18 , (S , ((\s -> D (unlift18 s)) , Void )))

[|_|]18_ : Desc18 -> Set18 -> Set18
[| con (DescId18 , Void) |]18 Z = Z
[| con (DescConst18 , ( S , Void)) |]18 Z = S
[| con (DescProd18 , (D , ( D' , Void ))) |]18 Z = [| D |]18 Z *18 [| D' |]18 Z
[| con (DescSigma18 , (S , (T , Void))) |]18 Z =  Sigma18 S (\s -> [| T (lifter s) |]18 Z )
[| con (DescPi18 , (S , (T , Void))) |]18 Z =  (s : S) -> [| T (lifter s) |]18 Z

data Mu18 (D : Desc18) : Set18 where
    con : [| D |]18 (Mu18 D) -> Mu18 D

data DescDef17 : Set18 where
    DescId17 : DescDef17
    DescConst17 : DescDef17
    DescProd17 : DescDef17
    DescSigma17 : DescDef17
    DescPi17 : DescDef17

data Lift17 (A : Set17) : Set18 where
    lifter : A -> Lift17 A

unlift17 : {A : Set17} -> Lift17 A -> A
unlift17 (lifter a) = a

descCases17 : DescDef17 -> Desc18
descCases17 DescId17 = const18 Unit18
descCases17 DescConst17 = sigma18 Set17 (\_ -> const18 Unit18)
descCases17 DescProd17 = prod18 id18 (prod18 id18 (const18 Unit18))
descCases17 DescSigma17 = sigma18 Set17 (\S -> prod18 (pi18 (Lift17 S)  (\_ -> id18)) (const18 Unit18))
descCases17 DescPi17 = sigma18 Set17 (\S -> prod18 (pi18 (Lift17 S) (\_ -> id18)) (const18 Unit18))

DescD17 : Desc18
DescD17 = sigma18 DescDef17 descCases17

Desc17 : Set18
Desc17 = Mu18 DescD17

id17 : Desc17
id17 = con (DescId17 , Void)

const17 : Set17 -> Desc17
const17 K = con (DescConst17 , (K , Void))

prod17 : (D D' : Desc17) -> Desc17
prod17 D D' = con (DescProd17 , (D , ( D' , Void )))

sigma17 : (S : Set17)(D : S -> Desc17) -> Desc17
sigma17 S D = con (DescSigma17 , (S , ((\s -> D (unlift17 s)) , Void )))

pi17 : (S : Set17)(D : S -> Desc17) -> Desc17
pi17 S D = con (DescPi17 , (S , ((\s -> D (unlift17 s)) , Void )))

[|_|]17_ : Desc17 -> Set17 -> Set17
[| con (DescId17 , Void) |]17 Z = Z
[| con (DescConst17 , ( S , Void)) |]17 Z = S
[| con (DescProd17 , (D , ( D' , Void ))) |]17 Z = [| D |]17 Z *17 [| D' |]17 Z
[| con (DescSigma17 , (S , (T , Void))) |]17 Z =  Sigma17 S (\s -> [| T (lifter s) |]17 Z )
[| con (DescPi17 , (S , (T , Void))) |]17 Z =  (s : S) -> [| T (lifter s) |]17 Z

data Mu17 (D : Desc17) : Set17 where
    con : [| D |]17 (Mu17 D) -> Mu17 D

data DescDef16 : Set17 where
    DescId16 : DescDef16
    DescConst16 : DescDef16
    DescProd16 : DescDef16
    DescSigma16 : DescDef16
    DescPi16 : DescDef16

data Lift16 (A : Set16) : Set17 where
    lifter : A -> Lift16 A

unlift16 : {A : Set16} -> Lift16 A -> A
unlift16 (lifter a) = a

descCases16 : DescDef16 -> Desc17
descCases16 DescId16 = const17 Unit17
descCases16 DescConst16 = sigma17 Set16 (\_ -> const17 Unit17)
descCases16 DescProd16 = prod17 id17 (prod17 id17 (const17 Unit17))
descCases16 DescSigma16 = sigma17 Set16 (\S -> prod17 (pi17 (Lift16 S)  (\_ -> id17)) (const17 Unit17))
descCases16 DescPi16 = sigma17 Set16 (\S -> prod17 (pi17 (Lift16 S) (\_ -> id17)) (const17 Unit17))

DescD16 : Desc17
DescD16 = sigma17 DescDef16 descCases16

Desc16 : Set17
Desc16 = Mu17 DescD16

id16 : Desc16
id16 = con (DescId16 , Void)

const16 : Set16 -> Desc16
const16 K = con (DescConst16 , (K , Void))

prod16 : (D D' : Desc16) -> Desc16
prod16 D D' = con (DescProd16 , (D , ( D' , Void )))

sigma16 : (S : Set16)(D : S -> Desc16) -> Desc16
sigma16 S D = con (DescSigma16 , (S , ((\s -> D (unlift16 s)) , Void )))

pi16 : (S : Set16)(D : S -> Desc16) -> Desc16
pi16 S D = con (DescPi16 , (S , ((\s -> D (unlift16 s)) , Void )))

[|_|]16_ : Desc16 -> Set16 -> Set16
[| con (DescId16 , Void) |]16 Z = Z
[| con (DescConst16 , ( S , Void)) |]16 Z = S
[| con (DescProd16 , (D , ( D' , Void ))) |]16 Z = [| D |]16 Z *16 [| D' |]16 Z
[| con (DescSigma16 , (S , (T , Void))) |]16 Z =  Sigma16 S (\s -> [| T (lifter s) |]16 Z )
[| con (DescPi16 , (S , (T , Void))) |]16 Z =  (s : S) -> [| T (lifter s) |]16 Z

data Mu16 (D : Desc16) : Set16 where
    con : [| D |]16 (Mu16 D) -> Mu16 D

data DescDef15 : Set16 where
    DescId15 : DescDef15
    DescConst15 : DescDef15
    DescProd15 : DescDef15
    DescSigma15 : DescDef15
    DescPi15 : DescDef15

data Lift15 (A : Set15) : Set16 where
    lifter : A -> Lift15 A

unlift15 : {A : Set15} -> Lift15 A -> A
unlift15 (lifter a) = a

descCases15 : DescDef15 -> Desc16
descCases15 DescId15 = const16 Unit16
descCases15 DescConst15 = sigma16 Set15 (\_ -> const16 Unit16)
descCases15 DescProd15 = prod16 id16 (prod16 id16 (const16 Unit16))
descCases15 DescSigma15 = sigma16 Set15 (\S -> prod16 (pi16 (Lift15 S)  (\_ -> id16)) (const16 Unit16))
descCases15 DescPi15 = sigma16 Set15 (\S -> prod16 (pi16 (Lift15 S) (\_ -> id16)) (const16 Unit16))

DescD15 : Desc16
DescD15 = sigma16 DescDef15 descCases15

Desc15 : Set16
Desc15 = Mu16 DescD15

id15 : Desc15
id15 = con (DescId15 , Void)

const15 : Set15 -> Desc15
const15 K = con (DescConst15 , (K , Void))

prod15 : (D D' : Desc15) -> Desc15
prod15 D D' = con (DescProd15 , (D , ( D' , Void )))

sigma15 : (S : Set15)(D : S -> Desc15) -> Desc15
sigma15 S D = con (DescSigma15 , (S , ((\s -> D (unlift15 s)) , Void )))

pi15 : (S : Set15)(D : S -> Desc15) -> Desc15
pi15 S D = con (DescPi15 , (S , ((\s -> D (unlift15 s)) , Void )))

[|_|]15_ : Desc15 -> Set15 -> Set15
[| con (DescId15 , Void) |]15 Z = Z
[| con (DescConst15 , ( S , Void)) |]15 Z = S
[| con (DescProd15 , (D , ( D' , Void ))) |]15 Z = [| D |]15 Z *15 [| D' |]15 Z
[| con (DescSigma15 , (S , (T , Void))) |]15 Z =  Sigma15 S (\s -> [| T (lifter s) |]15 Z )
[| con (DescPi15 , (S , (T , Void))) |]15 Z =  (s : S) -> [| T (lifter s) |]15 Z

data Mu15 (D : Desc15) : Set15 where
    con : [| D |]15 (Mu15 D) -> Mu15 D

data DescDef14 : Set15 where
    DescId14 : DescDef14
    DescConst14 : DescDef14
    DescProd14 : DescDef14
    DescSigma14 : DescDef14
    DescPi14 : DescDef14

data Lift14 (A : Set14) : Set15 where
    lifter : A -> Lift14 A

unlift14 : {A : Set14} -> Lift14 A -> A
unlift14 (lifter a) = a

descCases14 : DescDef14 -> Desc15
descCases14 DescId14 = const15 Unit15
descCases14 DescConst14 = sigma15 Set14 (\_ -> const15 Unit15)
descCases14 DescProd14 = prod15 id15 (prod15 id15 (const15 Unit15))
descCases14 DescSigma14 = sigma15 Set14 (\S -> prod15 (pi15 (Lift14 S)  (\_ -> id15)) (const15 Unit15))
descCases14 DescPi14 = sigma15 Set14 (\S -> prod15 (pi15 (Lift14 S) (\_ -> id15)) (const15 Unit15))

DescD14 : Desc15
DescD14 = sigma15 DescDef14 descCases14

Desc14 : Set15
Desc14 = Mu15 DescD14

id14 : Desc14
id14 = con (DescId14 , Void)

const14 : Set14 -> Desc14
const14 K = con (DescConst14 , (K , Void))

prod14 : (D D' : Desc14) -> Desc14
prod14 D D' = con (DescProd14 , (D , ( D' , Void )))

sigma14 : (S : Set14)(D : S -> Desc14) -> Desc14
sigma14 S D = con (DescSigma14 , (S , ((\s -> D (unlift14 s)) , Void )))

pi14 : (S : Set14)(D : S -> Desc14) -> Desc14
pi14 S D = con (DescPi14 , (S , ((\s -> D (unlift14 s)) , Void )))

[|_|]14_ : Desc14 -> Set14 -> Set14
[| con (DescId14 , Void) |]14 Z = Z
[| con (DescConst14 , ( S , Void)) |]14 Z = S
[| con (DescProd14 , (D , ( D' , Void ))) |]14 Z = [| D |]14 Z *14 [| D' |]14 Z
[| con (DescSigma14 , (S , (T , Void))) |]14 Z =  Sigma14 S (\s -> [| T (lifter s) |]14 Z )
[| con (DescPi14 , (S , (T , Void))) |]14 Z =  (s : S) -> [| T (lifter s) |]14 Z

data Mu14 (D : Desc14) : Set14 where
    con : [| D |]14 (Mu14 D) -> Mu14 D

data DescDef13 : Set14 where
    DescId13 : DescDef13
    DescConst13 : DescDef13
    DescProd13 : DescDef13
    DescSigma13 : DescDef13
    DescPi13 : DescDef13

data Lift13 (A : Set13) : Set14 where
    lifter : A -> Lift13 A

unlift13 : {A : Set13} -> Lift13 A -> A
unlift13 (lifter a) = a

descCases13 : DescDef13 -> Desc14
descCases13 DescId13 = const14 Unit14
descCases13 DescConst13 = sigma14 Set13 (\_ -> const14 Unit14)
descCases13 DescProd13 = prod14 id14 (prod14 id14 (const14 Unit14))
descCases13 DescSigma13 = sigma14 Set13 (\S -> prod14 (pi14 (Lift13 S)  (\_ -> id14)) (const14 Unit14))
descCases13 DescPi13 = sigma14 Set13 (\S -> prod14 (pi14 (Lift13 S) (\_ -> id14)) (const14 Unit14))

DescD13 : Desc14
DescD13 = sigma14 DescDef13 descCases13

Desc13 : Set14
Desc13 = Mu14 DescD13

id13 : Desc13
id13 = con (DescId13 , Void)

const13 : Set13 -> Desc13
const13 K = con (DescConst13 , (K , Void))

prod13 : (D D' : Desc13) -> Desc13
prod13 D D' = con (DescProd13 , (D , ( D' , Void )))

sigma13 : (S : Set13)(D : S -> Desc13) -> Desc13
sigma13 S D = con (DescSigma13 , (S , ((\s -> D (unlift13 s)) , Void )))

pi13 : (S : Set13)(D : S -> Desc13) -> Desc13
pi13 S D = con (DescPi13 , (S , ((\s -> D (unlift13 s)) , Void )))

[|_|]13_ : Desc13 -> Set13 -> Set13
[| con (DescId13 , Void) |]13 Z = Z
[| con (DescConst13 , ( S , Void)) |]13 Z = S
[| con (DescProd13 , (D , ( D' , Void ))) |]13 Z = [| D |]13 Z *13 [| D' |]13 Z
[| con (DescSigma13 , (S , (T , Void))) |]13 Z =  Sigma13 S (\s -> [| T (lifter s) |]13 Z )
[| con (DescPi13 , (S , (T , Void))) |]13 Z =  (s : S) -> [| T (lifter s) |]13 Z

data Mu13 (D : Desc13) : Set13 where
    con : [| D |]13 (Mu13 D) -> Mu13 D

data DescDef12 : Set13 where
    DescId12 : DescDef12
    DescConst12 : DescDef12
    DescProd12 : DescDef12
    DescSigma12 : DescDef12
    DescPi12 : DescDef12

data Lift12 (A : Set12) : Set13 where
    lifter : A -> Lift12 A

unlift12 : {A : Set12} -> Lift12 A -> A
unlift12 (lifter a) = a

descCases12 : DescDef12 -> Desc13
descCases12 DescId12 = const13 Unit13
descCases12 DescConst12 = sigma13 Set12 (\_ -> const13 Unit13)
descCases12 DescProd12 = prod13 id13 (prod13 id13 (const13 Unit13))
descCases12 DescSigma12 = sigma13 Set12 (\S -> prod13 (pi13 (Lift12 S)  (\_ -> id13)) (const13 Unit13))
descCases12 DescPi12 = sigma13 Set12 (\S -> prod13 (pi13 (Lift12 S) (\_ -> id13)) (const13 Unit13))

DescD12 : Desc13
DescD12 = sigma13 DescDef12 descCases12

Desc12 : Set13
Desc12 = Mu13 DescD12

id12 : Desc12
id12 = con (DescId12 , Void)

const12 : Set12 -> Desc12
const12 K = con (DescConst12 , (K , Void))

prod12 : (D D' : Desc12) -> Desc12
prod12 D D' = con (DescProd12 , (D , ( D' , Void )))

sigma12 : (S : Set12)(D : S -> Desc12) -> Desc12
sigma12 S D = con (DescSigma12 , (S , ((\s -> D (unlift12 s)) , Void )))

pi12 : (S : Set12)(D : S -> Desc12) -> Desc12
pi12 S D = con (DescPi12 , (S , ((\s -> D (unlift12 s)) , Void )))

[|_|]12_ : Desc12 -> Set12 -> Set12
[| con (DescId12 , Void) |]12 Z = Z
[| con (DescConst12 , ( S , Void)) |]12 Z = S
[| con (DescProd12 , (D , ( D' , Void ))) |]12 Z = [| D |]12 Z *12 [| D' |]12 Z
[| con (DescSigma12 , (S , (T , Void))) |]12 Z =  Sigma12 S (\s -> [| T (lifter s) |]12 Z )
[| con (DescPi12 , (S , (T , Void))) |]12 Z =  (s : S) -> [| T (lifter s) |]12 Z

data Mu12 (D : Desc12) : Set12 where
    con : [| D |]12 (Mu12 D) -> Mu12 D

data DescDef11 : Set12 where
    DescId11 : DescDef11
    DescConst11 : DescDef11
    DescProd11 : DescDef11
    DescSigma11 : DescDef11
    DescPi11 : DescDef11

data Lift11 (A : Set11) : Set12 where
    lifter : A -> Lift11 A

unlift11 : {A : Set11} -> Lift11 A -> A
unlift11 (lifter a) = a

descCases11 : DescDef11 -> Desc12
descCases11 DescId11 = const12 Unit12
descCases11 DescConst11 = sigma12 Set11 (\_ -> const12 Unit12)
descCases11 DescProd11 = prod12 id12 (prod12 id12 (const12 Unit12))
descCases11 DescSigma11 = sigma12 Set11 (\S -> prod12 (pi12 (Lift11 S)  (\_ -> id12)) (const12 Unit12))
descCases11 DescPi11 = sigma12 Set11 (\S -> prod12 (pi12 (Lift11 S) (\_ -> id12)) (const12 Unit12))

DescD11 : Desc12
DescD11 = sigma12 DescDef11 descCases11

Desc11 : Set12
Desc11 = Mu12 DescD11

id11 : Desc11
id11 = con (DescId11 , Void)

const11 : Set11 -> Desc11
const11 K = con (DescConst11 , (K , Void))

prod11 : (D D' : Desc11) -> Desc11
prod11 D D' = con (DescProd11 , (D , ( D' , Void )))

sigma11 : (S : Set11)(D : S -> Desc11) -> Desc11
sigma11 S D = con (DescSigma11 , (S , ((\s -> D (unlift11 s)) , Void )))

pi11 : (S : Set11)(D : S -> Desc11) -> Desc11
pi11 S D = con (DescPi11 , (S , ((\s -> D (unlift11 s)) , Void )))

[|_|]11_ : Desc11 -> Set11 -> Set11
[| con (DescId11 , Void) |]11 Z = Z
[| con (DescConst11 , ( S , Void)) |]11 Z = S
[| con (DescProd11 , (D , ( D' , Void ))) |]11 Z = [| D |]11 Z *11 [| D' |]11 Z
[| con (DescSigma11 , (S , (T , Void))) |]11 Z =  Sigma11 S (\s -> [| T (lifter s) |]11 Z )
[| con (DescPi11 , (S , (T , Void))) |]11 Z =  (s : S) -> [| T (lifter s) |]11 Z

data Mu11 (D : Desc11) : Set11 where
    con : [| D |]11 (Mu11 D) -> Mu11 D

data DescDef10 : Set11 where
    DescId10 : DescDef10
    DescConst10 : DescDef10
    DescProd10 : DescDef10
    DescSigma10 : DescDef10
    DescPi10 : DescDef10

data Lift10 (A : Set10) : Set11 where
    lifter : A -> Lift10 A

unlift10 : {A : Set10} -> Lift10 A -> A
unlift10 (lifter a) = a

descCases10 : DescDef10 -> Desc11
descCases10 DescId10 = const11 Unit11
descCases10 DescConst10 = sigma11 Set10 (\_ -> const11 Unit11)
descCases10 DescProd10 = prod11 id11 (prod11 id11 (const11 Unit11))
descCases10 DescSigma10 = sigma11 Set10 (\S -> prod11 (pi11 (Lift10 S)  (\_ -> id11)) (const11 Unit11))
descCases10 DescPi10 = sigma11 Set10 (\S -> prod11 (pi11 (Lift10 S) (\_ -> id11)) (const11 Unit11))

DescD10 : Desc11
DescD10 = sigma11 DescDef10 descCases10

Desc10 : Set11
Desc10 = Mu11 DescD10

id10 : Desc10
id10 = con (DescId10 , Void)

const10 : Set10 -> Desc10
const10 K = con (DescConst10 , (K , Void))

prod10 : (D D' : Desc10) -> Desc10
prod10 D D' = con (DescProd10 , (D , ( D' , Void )))

sigma10 : (S : Set10)(D : S -> Desc10) -> Desc10
sigma10 S D = con (DescSigma10 , (S , ((\s -> D (unlift10 s)) , Void )))

pi10 : (S : Set10)(D : S -> Desc10) -> Desc10
pi10 S D = con (DescPi10 , (S , ((\s -> D (unlift10 s)) , Void )))

[|_|]10_ : Desc10 -> Set10 -> Set10
[| con (DescId10 , Void) |]10 Z = Z
[| con (DescConst10 , ( S , Void)) |]10 Z = S
[| con (DescProd10 , (D , ( D' , Void ))) |]10 Z = [| D |]10 Z *10 [| D' |]10 Z
[| con (DescSigma10 , (S , (T , Void))) |]10 Z =  Sigma10 S (\s -> [| T (lifter s) |]10 Z )
[| con (DescPi10 , (S , (T , Void))) |]10 Z =  (s : S) -> [| T (lifter s) |]10 Z

data Mu10 (D : Desc10) : Set10 where
    con : [| D |]10 (Mu10 D) -> Mu10 D

data DescDef9 : Set10 where
    DescId9 : DescDef9
    DescConst9 : DescDef9
    DescProd9 : DescDef9
    DescSigma9 : DescDef9
    DescPi9 : DescDef9

data Lift9 (A : Set9) : Set10 where
    lifter : A -> Lift9 A

unlift9 : {A : Set9} -> Lift9 A -> A
unlift9 (lifter a) = a

descCases9 : DescDef9 -> Desc10
descCases9 DescId9 = const10 Unit10
descCases9 DescConst9 = sigma10 Set9 (\_ -> const10 Unit10)
descCases9 DescProd9 = prod10 id10 (prod10 id10 (const10 Unit10))
descCases9 DescSigma9 = sigma10 Set9 (\S -> prod10 (pi10 (Lift9 S)  (\_ -> id10)) (const10 Unit10))
descCases9 DescPi9 = sigma10 Set9 (\S -> prod10 (pi10 (Lift9 S) (\_ -> id10)) (const10 Unit10))

DescD9 : Desc10
DescD9 = sigma10 DescDef9 descCases9

Desc9 : Set10
Desc9 = Mu10 DescD9

id9 : Desc9
id9 = con (DescId9 , Void)

const9 : Set9 -> Desc9
const9 K = con (DescConst9 , (K , Void))

prod9 : (D D' : Desc9) -> Desc9
prod9 D D' = con (DescProd9 , (D , ( D' , Void )))

sigma9 : (S : Set9)(D : S -> Desc9) -> Desc9
sigma9 S D = con (DescSigma9 , (S , ((\s -> D (unlift9 s)) , Void )))

pi9 : (S : Set9)(D : S -> Desc9) -> Desc9
pi9 S D = con (DescPi9 , (S , ((\s -> D (unlift9 s)) , Void )))

[|_|]9_ : Desc9 -> Set9 -> Set9
[| con (DescId9 , Void) |]9 Z = Z
[| con (DescConst9 , ( S , Void)) |]9 Z = S
[| con (DescProd9 , (D , ( D' , Void ))) |]9 Z = [| D |]9 Z *9 [| D' |]9 Z
[| con (DescSigma9 , (S , (T , Void))) |]9 Z =  Sigma9 S (\s -> [| T (lifter s) |]9 Z )
[| con (DescPi9 , (S , (T , Void))) |]9 Z =  (s : S) -> [| T (lifter s) |]9 Z

data Mu9 (D : Desc9) : Set9 where
    con : [| D |]9 (Mu9 D) -> Mu9 D

data DescDef8 : Set9 where
    DescId8 : DescDef8
    DescConst8 : DescDef8
    DescProd8 : DescDef8
    DescSigma8 : DescDef8
    DescPi8 : DescDef8

data Lift8 (A : Set8) : Set9 where
    lifter : A -> Lift8 A

unlift8 : {A : Set8} -> Lift8 A -> A
unlift8 (lifter a) = a

descCases8 : DescDef8 -> Desc9
descCases8 DescId8 = const9 Unit9
descCases8 DescConst8 = sigma9 Set8 (\_ -> const9 Unit9)
descCases8 DescProd8 = prod9 id9 (prod9 id9 (const9 Unit9))
descCases8 DescSigma8 = sigma9 Set8 (\S -> prod9 (pi9 (Lift8 S)  (\_ -> id9)) (const9 Unit9))
descCases8 DescPi8 = sigma9 Set8 (\S -> prod9 (pi9 (Lift8 S) (\_ -> id9)) (const9 Unit9))

DescD8 : Desc9
DescD8 = sigma9 DescDef8 descCases8

Desc8 : Set9
Desc8 = Mu9 DescD8

id8 : Desc8
id8 = con (DescId8 , Void)

const8 : Set8 -> Desc8
const8 K = con (DescConst8 , (K , Void))

prod8 : (D D' : Desc8) -> Desc8
prod8 D D' = con (DescProd8 , (D , ( D' , Void )))

sigma8 : (S : Set8)(D : S -> Desc8) -> Desc8
sigma8 S D = con (DescSigma8 , (S , ((\s -> D (unlift8 s)) , Void )))

pi8 : (S : Set8)(D : S -> Desc8) -> Desc8
pi8 S D = con (DescPi8 , (S , ((\s -> D (unlift8 s)) , Void )))

[|_|]8_ : Desc8 -> Set8 -> Set8
[| con (DescId8 , Void) |]8 Z = Z
[| con (DescConst8 , ( S , Void)) |]8 Z = S
[| con (DescProd8 , (D , ( D' , Void ))) |]8 Z = [| D |]8 Z *8 [| D' |]8 Z
[| con (DescSigma8 , (S , (T , Void))) |]8 Z =  Sigma8 S (\s -> [| T (lifter s) |]8 Z )
[| con (DescPi8 , (S , (T , Void))) |]8 Z =  (s : S) -> [| T (lifter s) |]8 Z

data Mu8 (D : Desc8) : Set8 where
    con : [| D |]8 (Mu8 D) -> Mu8 D

data DescDef7 : Set8 where
    DescId7 : DescDef7
    DescConst7 : DescDef7
    DescProd7 : DescDef7
    DescSigma7 : DescDef7
    DescPi7 : DescDef7

data Lift7 (A : Set7) : Set8 where
    lifter : A -> Lift7 A

unlift7 : {A : Set7} -> Lift7 A -> A
unlift7 (lifter a) = a

descCases7 : DescDef7 -> Desc8
descCases7 DescId7 = const8 Unit8
descCases7 DescConst7 = sigma8 Set7 (\_ -> const8 Unit8)
descCases7 DescProd7 = prod8 id8 (prod8 id8 (const8 Unit8))
descCases7 DescSigma7 = sigma8 Set7 (\S -> prod8 (pi8 (Lift7 S)  (\_ -> id8)) (const8 Unit8))
descCases7 DescPi7 = sigma8 Set7 (\S -> prod8 (pi8 (Lift7 S) (\_ -> id8)) (const8 Unit8))

DescD7 : Desc8
DescD7 = sigma8 DescDef7 descCases7

Desc7 : Set8
Desc7 = Mu8 DescD7

id7 : Desc7
id7 = con (DescId7 , Void)

const7 : Set7 -> Desc7
const7 K = con (DescConst7 , (K , Void))

prod7 : (D D' : Desc7) -> Desc7
prod7 D D' = con (DescProd7 , (D , ( D' , Void )))

sigma7 : (S : Set7)(D : S -> Desc7) -> Desc7
sigma7 S D = con (DescSigma7 , (S , ((\s -> D (unlift7 s)) , Void )))

pi7 : (S : Set7)(D : S -> Desc7) -> Desc7
pi7 S D = con (DescPi7 , (S , ((\s -> D (unlift7 s)) , Void )))

[|_|]7_ : Desc7 -> Set7 -> Set7
[| con (DescId7 , Void) |]7 Z = Z
[| con (DescConst7 , ( S , Void)) |]7 Z = S
[| con (DescProd7 , (D , ( D' , Void ))) |]7 Z = [| D |]7 Z *7 [| D' |]7 Z
[| con (DescSigma7 , (S , (T , Void))) |]7 Z =  Sigma7 S (\s -> [| T (lifter s) |]7 Z )
[| con (DescPi7 , (S , (T , Void))) |]7 Z =  (s : S) -> [| T (lifter s) |]7 Z

data Mu7 (D : Desc7) : Set7 where
    con : [| D |]7 (Mu7 D) -> Mu7 D

data DescDef6 : Set7 where
    DescId6 : DescDef6
    DescConst6 : DescDef6
    DescProd6 : DescDef6
    DescSigma6 : DescDef6
    DescPi6 : DescDef6

data Lift6 (A : Set6) : Set7 where
    lifter : A -> Lift6 A

unlift6 : {A : Set6} -> Lift6 A -> A
unlift6 (lifter a) = a

descCases6 : DescDef6 -> Desc7
descCases6 DescId6 = const7 Unit7
descCases6 DescConst6 = sigma7 Set6 (\_ -> const7 Unit7)
descCases6 DescProd6 = prod7 id7 (prod7 id7 (const7 Unit7))
descCases6 DescSigma6 = sigma7 Set6 (\S -> prod7 (pi7 (Lift6 S)  (\_ -> id7)) (const7 Unit7))
descCases6 DescPi6 = sigma7 Set6 (\S -> prod7 (pi7 (Lift6 S) (\_ -> id7)) (const7 Unit7))

DescD6 : Desc7
DescD6 = sigma7 DescDef6 descCases6

Desc6 : Set7
Desc6 = Mu7 DescD6

id6 : Desc6
id6 = con (DescId6 , Void)

const6 : Set6 -> Desc6
const6 K = con (DescConst6 , (K , Void))

prod6 : (D D' : Desc6) -> Desc6
prod6 D D' = con (DescProd6 , (D , ( D' , Void )))

sigma6 : (S : Set6)(D : S -> Desc6) -> Desc6
sigma6 S D = con (DescSigma6 , (S , ((\s -> D (unlift6 s)) , Void )))

pi6 : (S : Set6)(D : S -> Desc6) -> Desc6
pi6 S D = con (DescPi6 , (S , ((\s -> D (unlift6 s)) , Void )))

[|_|]6_ : Desc6 -> Set6 -> Set6
[| con (DescId6 , Void) |]6 Z = Z
[| con (DescConst6 , ( S , Void)) |]6 Z = S
[| con (DescProd6 , (D , ( D' , Void ))) |]6 Z = [| D |]6 Z *6 [| D' |]6 Z
[| con (DescSigma6 , (S , (T , Void))) |]6 Z =  Sigma6 S (\s -> [| T (lifter s) |]6 Z )
[| con (DescPi6 , (S , (T , Void))) |]6 Z =  (s : S) -> [| T (lifter s) |]6 Z

data Mu6 (D : Desc6) : Set6 where
    con : [| D |]6 (Mu6 D) -> Mu6 D

data DescDef5 : Set6 where
    DescId5 : DescDef5
    DescConst5 : DescDef5
    DescProd5 : DescDef5
    DescSigma5 : DescDef5
    DescPi5 : DescDef5

data Lift5 (A : Set5) : Set6 where
    lifter : A -> Lift5 A

unlift5 : {A : Set5} -> Lift5 A -> A
unlift5 (lifter a) = a

descCases5 : DescDef5 -> Desc6
descCases5 DescId5 = const6 Unit6
descCases5 DescConst5 = sigma6 Set5 (\_ -> const6 Unit6)
descCases5 DescProd5 = prod6 id6 (prod6 id6 (const6 Unit6))
descCases5 DescSigma5 = sigma6 Set5 (\S -> prod6 (pi6 (Lift5 S)  (\_ -> id6)) (const6 Unit6))
descCases5 DescPi5 = sigma6 Set5 (\S -> prod6 (pi6 (Lift5 S) (\_ -> id6)) (const6 Unit6))

DescD5 : Desc6
DescD5 = sigma6 DescDef5 descCases5

Desc5 : Set6
Desc5 = Mu6 DescD5

id5 : Desc5
id5 = con (DescId5 , Void)

const5 : Set5 -> Desc5
const5 K = con (DescConst5 , (K , Void))

prod5 : (D D' : Desc5) -> Desc5
prod5 D D' = con (DescProd5 , (D , ( D' , Void )))

sigma5 : (S : Set5)(D : S -> Desc5) -> Desc5
sigma5 S D = con (DescSigma5 , (S , ((\s -> D (unlift5 s)) , Void )))

pi5 : (S : Set5)(D : S -> Desc5) -> Desc5
pi5 S D = con (DescPi5 , (S , ((\s -> D (unlift5 s)) , Void )))

[|_|]5_ : Desc5 -> Set5 -> Set5
[| con (DescId5 , Void) |]5 Z = Z
[| con (DescConst5 , ( S , Void)) |]5 Z = S
[| con (DescProd5 , (D , ( D' , Void ))) |]5 Z = [| D |]5 Z *5 [| D' |]5 Z
[| con (DescSigma5 , (S , (T , Void))) |]5 Z =  Sigma5 S (\s -> [| T (lifter s) |]5 Z )
[| con (DescPi5 , (S , (T , Void))) |]5 Z =  (s : S) -> [| T (lifter s) |]5 Z

data Mu5 (D : Desc5) : Set5 where
    con : [| D |]5 (Mu5 D) -> Mu5 D

data DescDef4 : Set5 where
    DescId4 : DescDef4
    DescConst4 : DescDef4
    DescProd4 : DescDef4
    DescSigma4 : DescDef4
    DescPi4 : DescDef4

data Lift4 (A : Set4) : Set5 where
    lifter : A -> Lift4 A

unlift4 : {A : Set4} -> Lift4 A -> A
unlift4 (lifter a) = a

descCases4 : DescDef4 -> Desc5
descCases4 DescId4 = const5 Unit5
descCases4 DescConst4 = sigma5 Set4 (\_ -> const5 Unit5)
descCases4 DescProd4 = prod5 id5 (prod5 id5 (const5 Unit5))
descCases4 DescSigma4 = sigma5 Set4 (\S -> prod5 (pi5 (Lift4 S)  (\_ -> id5)) (const5 Unit5))
descCases4 DescPi4 = sigma5 Set4 (\S -> prod5 (pi5 (Lift4 S) (\_ -> id5)) (const5 Unit5))

DescD4 : Desc5
DescD4 = sigma5 DescDef4 descCases4

Desc4 : Set5
Desc4 = Mu5 DescD4

id4 : Desc4
id4 = con (DescId4 , Void)

const4 : Set4 -> Desc4
const4 K = con (DescConst4 , (K , Void))

prod4 : (D D' : Desc4) -> Desc4
prod4 D D' = con (DescProd4 , (D , ( D' , Void )))

sigma4 : (S : Set4)(D : S -> Desc4) -> Desc4
sigma4 S D = con (DescSigma4 , (S , ((\s -> D (unlift4 s)) , Void )))

pi4 : (S : Set4)(D : S -> Desc4) -> Desc4
pi4 S D = con (DescPi4 , (S , ((\s -> D (unlift4 s)) , Void )))

[|_|]4_ : Desc4 -> Set4 -> Set4
[| con (DescId4 , Void) |]4 Z = Z
[| con (DescConst4 , ( S , Void)) |]4 Z = S
[| con (DescProd4 , (D , ( D' , Void ))) |]4 Z = [| D |]4 Z *4 [| D' |]4 Z
[| con (DescSigma4 , (S , (T , Void))) |]4 Z =  Sigma4 S (\s -> [| T (lifter s) |]4 Z )
[| con (DescPi4 , (S , (T , Void))) |]4 Z =  (s : S) -> [| T (lifter s) |]4 Z

data Mu4 (D : Desc4) : Set4 where
    con : [| D |]4 (Mu4 D) -> Mu4 D

data DescDef3 : Set4 where
    DescId3 : DescDef3
    DescConst3 : DescDef3
    DescProd3 : DescDef3
    DescSigma3 : DescDef3
    DescPi3 : DescDef3

data Lift3 (A : Set3) : Set4 where
    lifter : A -> Lift3 A

unlift3 : {A : Set3} -> Lift3 A -> A
unlift3 (lifter a) = a

descCases3 : DescDef3 -> Desc4
descCases3 DescId3 = const4 Unit4
descCases3 DescConst3 = sigma4 Set3 (\_ -> const4 Unit4)
descCases3 DescProd3 = prod4 id4 (prod4 id4 (const4 Unit4))
descCases3 DescSigma3 = sigma4 Set3 (\S -> prod4 (pi4 (Lift3 S)  (\_ -> id4)) (const4 Unit4))
descCases3 DescPi3 = sigma4 Set3 (\S -> prod4 (pi4 (Lift3 S) (\_ -> id4)) (const4 Unit4))

DescD3 : Desc4
DescD3 = sigma4 DescDef3 descCases3

Desc3 : Set4
Desc3 = Mu4 DescD3

id3 : Desc3
id3 = con (DescId3 , Void)

const3 : Set3 -> Desc3
const3 K = con (DescConst3 , (K , Void))

prod3 : (D D' : Desc3) -> Desc3
prod3 D D' = con (DescProd3 , (D , ( D' , Void )))

sigma3 : (S : Set3)(D : S -> Desc3) -> Desc3
sigma3 S D = con (DescSigma3 , (S , ((\s -> D (unlift3 s)) , Void )))

pi3 : (S : Set3)(D : S -> Desc3) -> Desc3
pi3 S D = con (DescPi3 , (S , ((\s -> D (unlift3 s)) , Void )))

[|_|]3_ : Desc3 -> Set3 -> Set3
[| con (DescId3 , Void) |]3 Z = Z
[| con (DescConst3 , ( S , Void)) |]3 Z = S
[| con (DescProd3 , (D , ( D' , Void ))) |]3 Z = [| D |]3 Z *3 [| D' |]3 Z
[| con (DescSigma3 , (S , (T , Void))) |]3 Z =  Sigma3 S (\s -> [| T (lifter s) |]3 Z )
[| con (DescPi3 , (S , (T , Void))) |]3 Z =  (s : S) -> [| T (lifter s) |]3 Z

data Mu3 (D : Desc3) : Set3 where
    con : [| D |]3 (Mu3 D) -> Mu3 D

data DescDef2 : Set3 where
    DescId2 : DescDef2
    DescConst2 : DescDef2
    DescProd2 : DescDef2
    DescSigma2 : DescDef2
    DescPi2 : DescDef2

data Lift2 (A : Set2) : Set3 where
    lifter : A -> Lift2 A

unlift2 : {A : Set2} -> Lift2 A -> A
unlift2 (lifter a) = a

descCases2 : DescDef2 -> Desc3
descCases2 DescId2 = const3 Unit3
descCases2 DescConst2 = sigma3 Set2 (\_ -> const3 Unit3)
descCases2 DescProd2 = prod3 id3 (prod3 id3 (const3 Unit3))
descCases2 DescSigma2 = sigma3 Set2 (\S -> prod3 (pi3 (Lift2 S)  (\_ -> id3)) (const3 Unit3))
descCases2 DescPi2 = sigma3 Set2 (\S -> prod3 (pi3 (Lift2 S) (\_ -> id3)) (const3 Unit3))

DescD2 : Desc3
DescD2 = sigma3 DescDef2 descCases2

Desc2 : Set3
Desc2 = Mu3 DescD2

id2 : Desc2
id2 = con (DescId2 , Void)

const2 : Set2 -> Desc2
const2 K = con (DescConst2 , (K , Void))

prod2 : (D D' : Desc2) -> Desc2
prod2 D D' = con (DescProd2 , (D , ( D' , Void )))

sigma2 : (S : Set2)(D : S -> Desc2) -> Desc2
sigma2 S D = con (DescSigma2 , (S , ((\s -> D (unlift2 s)) , Void )))

pi2 : (S : Set2)(D : S -> Desc2) -> Desc2
pi2 S D = con (DescPi2 , (S , ((\s -> D (unlift2 s)) , Void )))

[|_|]2_ : Desc2 -> Set2 -> Set2
[| con (DescId2 , Void) |]2 Z = Z
[| con (DescConst2 , ( S , Void)) |]2 Z = S
[| con (DescProd2 , (D , ( D' , Void ))) |]2 Z = [| D |]2 Z *2 [| D' |]2 Z
[| con (DescSigma2 , (S , (T , Void))) |]2 Z =  Sigma2 S (\s -> [| T (lifter s) |]2 Z )
[| con (DescPi2 , (S , (T , Void))) |]2 Z =  (s : S) -> [| T (lifter s) |]2 Z

data Mu2 (D : Desc2) : Set2 where
    con : [| D |]2 (Mu2 D) -> Mu2 D

data DescDef1 : Set2 where
    DescId1 : DescDef1
    DescConst1 : DescDef1
    DescProd1 : DescDef1
    DescSigma1 : DescDef1
    DescPi1 : DescDef1

data Lift1 (A : Set1) : Set2 where
    lifter : A -> Lift1 A

unlift1 : {A : Set1} -> Lift1 A -> A
unlift1 (lifter a) = a

descCases1 : DescDef1 -> Desc2
descCases1 DescId1 = const2 Unit2
descCases1 DescConst1 = sigma2 Set1 (\_ -> const2 Unit2)
descCases1 DescProd1 = prod2 id2 (prod2 id2 (const2 Unit2))
descCases1 DescSigma1 = sigma2 Set1 (\S -> prod2 (pi2 (Lift1 S)  (\_ -> id2)) (const2 Unit2))
descCases1 DescPi1 = sigma2 Set1 (\S -> prod2 (pi2 (Lift1 S) (\_ -> id2)) (const2 Unit2))

DescD1 : Desc2
DescD1 = sigma2 DescDef1 descCases1

Desc1 : Set2
Desc1 = Mu2 DescD1

id1 : Desc1
id1 = con (DescId1 , Void)

const1 : Set1 -> Desc1
const1 K = con (DescConst1 , (K , Void))

prod1 : (D D' : Desc1) -> Desc1
prod1 D D' = con (DescProd1 , (D , ( D' , Void )))

sigma1 : (S : Set1)(D : S -> Desc1) -> Desc1
sigma1 S D = con (DescSigma1 , (S , ((\s -> D (unlift1 s)) , Void )))

pi1 : (S : Set1)(D : S -> Desc1) -> Desc1
pi1 S D = con (DescPi1 , (S , ((\s -> D (unlift1 s)) , Void )))

[|_|]1_ : Desc1 -> Set1 -> Set1
[| con (DescId1 , Void) |]1 Z = Z
[| con (DescConst1 , ( S , Void)) |]1 Z = S
[| con (DescProd1 , (D , ( D' , Void ))) |]1 Z = [| D |]1 Z *1 [| D' |]1 Z
[| con (DescSigma1 , (S , (T , Void))) |]1 Z =  Sigma1 S (\s -> [| T (lifter s) |]1 Z )
[| con (DescPi1 , (S , (T , Void))) |]1 Z =  (s : S) -> [| T (lifter s) |]1 Z

data Mu1 (D : Desc1) : Set1 where
    con : [| D |]1 (Mu1 D) -> Mu1 D

data DescDef0 : Set1 where
    DescId0 : DescDef0
    DescConst0 : DescDef0
    DescProd0 : DescDef0
    DescSigma0 : DescDef0
    DescPi0 : DescDef0

data Lift0 (A : Set0) : Set1 where
    lifter : A -> Lift0 A

unlift0 : {A : Set0} -> Lift0 A -> A
unlift0 (lifter a) = a

descCases0 : DescDef0 -> Desc1
descCases0 DescId0 = const1 Unit1
descCases0 DescConst0 = sigma1 Set0 (\_ -> const1 Unit1)
descCases0 DescProd0 = prod1 id1 (prod1 id1 (const1 Unit1))
descCases0 DescSigma0 = sigma1 Set0 (\S -> prod1 (pi1 (Lift0 S)  (\_ -> id1)) (const1 Unit1))
descCases0 DescPi0 = sigma1 Set0 (\S -> prod1 (pi1 (Lift0 S) (\_ -> id1)) (const1 Unit1))

DescD0 : Desc1
DescD0 = sigma1 DescDef0 descCases0

Desc0 : Set1
Desc0 = Mu1 DescD0

id0 : Desc0
id0 = con (DescId0 , Void)

const0 : Set0 -> Desc0
const0 K = con (DescConst0 , (K , Void))

prod0 : (D D' : Desc0) -> Desc0
prod0 D D' = con (DescProd0 , (D , ( D' , Void )))

sigma0 : (S : Set0)(D : S -> Desc0) -> Desc0
sigma0 S D = con (DescSigma0 , (S , ((\s -> D (unlift0 s)) , Void )))

pi0 : (S : Set0)(D : S -> Desc0) -> Desc0
pi0 S D = con (DescPi0 , (S , ((\s -> D (unlift0 s)) , Void )))

[|_|]0_ : Desc0 -> Set0 -> Set0
[| con (DescId0 , Void) |]0 Z = Z
[| con (DescConst0 , ( S , Void)) |]0 Z = S
[| con (DescProd0 , (D , ( D' , Void ))) |]0 Z = [| D |]0 Z *0 [| D' |]0 Z
[| con (DescSigma0 , (S , (T , Void))) |]0 Z =  Sigma0 S (\s -> [| T (lifter s) |]0 Z )
[| con (DescPi0 , (S , (T , Void))) |]0 Z =  (s : S) -> [| T (lifter s) |]0 Z

data Mu0 (D : Desc0) : Set0 where
    con : [| D |]0 (Mu0 D) -> Mu0 D
