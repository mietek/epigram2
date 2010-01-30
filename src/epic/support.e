append (x:String, y:String) -> String =
    foreign String "append" (x:String, y:String)
 
putStr (x:String) -> Unit =
    foreign Unit "putStr" (x:String)

putStrLn (x:String) -> Unit =
    putStr(append(x,"\n"))

__dumpData (x:Data) -> Unit =
    foreign Unit "dumpRecord" (x:Data); putStrLn("")

__switch (n:Int, ps:Data) -> Data =
   case n of {
      0 -> ps!0
    | Default -> __switch ((n-1), ps!1)
   }

__mapBox (D:Data, p:Data, d:Data) -> Data =
   case D!0 of
    { 0 -> []
    | 1 -> __mapBox((((D!1)!1)!0)(d!0), p, d!1)
    | 2 -> [__mapBoxH(p, d!0), __mapBox(((D!1)!1)!0, p, d!1)]
    | 3 -> [p(d!0), __mapBox((D!1)!0, p, d!1)]
    }

__mapBoxH (p:Data, f:Data, h:Data) -> Data = p(f(h))

__fold(D:Data, m:Data, x:Data) -> Data =
   m(x,__mapBox(D, __fold(D,m), x))

__map (D:Data, f:Data, x:Data) -> Data =
  case D!0 of
   { 0 -> []
   | 1 -> [x!0, __map((((D!1)!1)!0)(x!0), f, x!1)]
   | 2 -> [__mapH(f, x!0), __map(((D!1)!1)!0, f, x!1)]
   | 3 -> [f(x!0), __map((D!1)!0, f, x!1)]
   }

__imapBox (D:Data, p:Data, d:Data) -> Data =
   case D!0 of
    { 0 -> []
    | 1 -> __imapBox((((D!1)!1)!0)(d!0), p, d!1)
    | 2 -> [__imapBoxH(p, d!0, (d!1)!0), __mapBox((((D!1)!1)!1)!0, p, d!1)]
    | 3 -> [p([(D!1)!0,d!0]), __imapBox(((D!1)!1)!0, p, d!1)]
    }

__imapBoxH (p:Data, hi:Data, f:Data, h:Data) -> Data = p([hi(h),f(h)])

__ifold(D:Data, m:Data, i :Data, x:Data) -> Data =
   m(i,x,__imapBox(D(i), __ifold(D,m), x))

__lazyMap (D:Data, f:Data, x:Data) -> Data =
  case D!0 of
   { 0 -> []
   | 1 -> [x!0, __lazyMap((((D!1)!1)!0)(x!0), f, x!1)]
   | 2 -> [__mapH(f, x!0), __lazyMap(((D!1)!1)!0, f, x!1)]
   | 3 -> [lazy(f(x!0)), __lazyMap((D!1)!0, f, x!1)]
   }

__mapH (f:Data, x:Data, h:Data) -> Data = f(x(h))

__subst(D:Data, f:Data, t:Data) -> Data =
  case t!0 of
  { 0 -> f(t!1)
  | 1 -> [1, __map(D, __subst(D,f), t!1)]
  }

__elimMonad(D:Data, mv:Data, mc:Data, t:Data) -> Data =
  case t!0 of
  { 0 -> mv(t!1)
  | 1 -> mc(t!1, __mapBox(D, __elimMonad(D,mv,mc), t!1))
  }

__const(x:Data, y:Data) -> Data = x 

%inline __split(f:Data, y:Data) -> Data =
   f(y!0, y!1)

__coit(d:Data, f:Data, s:Data) -> Data = lazy(__map(d,__coit(d,f),f(s)))

-- Some tests

{-
Nat () -> Data = [1,NatP]

NatP (d:Data) -> Data = 
   case d of 
     { 0 -> [0]
     | 1 -> [3,[0]]
     }

plus (x:Data, y:Data) -> Data =
   __fold(Nat, plusH(y), x)

plusH (y:Data, x:Data, h:Data) -> Data =
   case x!0 of
     { 0 -> y
     | 1 -> [1,[h!0, []]]
     }

zero () -> Data = [0,[]]
succ (n:Data) -> Data = [1, [n, []]]


main () -> Unit = __dumpData(plus(succ(succ(zero)), succ(succ(zero))))

-}
