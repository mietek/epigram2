append (x:String, y:String) -> String =
    foreign String "append" (x:String, y:String)
 
putStr (x:String) -> Unit =
    foreign Unit "putStr" (x:String)

putStrLn (x:String) -> Unit =
    putStr(append(x,"\n"))

__dumpData (x:Data) -> Unit =
    foreign Unit "dumpRecord" (x:Data); putStrLn("")

__switch (ps:Data, n:Int) -> Data =
   case n of {
      0 -> ps!0
    | Default -> switch (ps!1, (n-1))
   }

__mapBox (D:Data, p:Data, d:Data) -> Data =
   case D!0 of
    { 0 -> []
    | 1 -> __mapBox((D!1)(d!0), p, d!1)
    | 2 -> [__mapBoxH(p, d!0), __mapBox(D!1, p, d!1)]
    | 3 -> [p(d!0), __mapBox(D!1, p, d!1)]
    }

__mapBoxH (p:Data, f:Data, h:Data) -> Data = p(f(h))

__elim(D:Data, m:Data, x:Data) -> Data =
   m(x,__mapBox(D, __elim(D,m), x))

__const(x:Data, y:Data) -> Data = x 

-- Some tests

{-
Nat () -> Data = [1,NatP]

NatP (d:Data) -> Data = 
   case d of 
     { 0 -> [0]
     | 1 -> [3,[0]]
     }

plus (x:Data, y:Data) -> Data =
   __elim(Nat, plusH(y), x)

plusH (y:Data, x:Data, h:Data) -> Data =
   case x!0 of
     { 0 -> y
     | 1 -> [1,[h!0, []]]
     }

zero () -> Data = [0,[]]
succ (n:Data) -> Data = [1, [n, []]]


main () -> Unit = __dumpData(plus(succ(succ(zero)), succ(succ(zero))))

-}
