append (x:String, y:String) -> String =
    foreign String "append" (x:String, y:String)
 
putStr (x:String) -> Unit =
    foreign Unit "putStr" (x:String)

putStrLn (x:String) -> Unit =
    putStr(append(x,"\n"))

dumpData (x:Data) -> Unit =
    foreign Unit "dumpRecord" (x:Data); putStrLn("")

switch (ps:Data, n:Int) -> Data =
   case n of {
      0 -> ps!0
    | Default -> switch (ps!1) (n-1)
   }
