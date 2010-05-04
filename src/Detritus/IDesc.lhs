>   makeElab loc (SET :>: DIMU Nothing iI d i) = do
>       GirlMother (nom := HOLE _ :<: ty) _ _ _ <- getMother
>       let fr = nom := FAKE :<: ty
>       xs <- getBoys
>       guard (not (null xs))
>       let lt = N (P fr $:$ (map (\x -> A (N (P x))) (init xs)))
>       let lv = evTm lt
>       (iI :=>: iIv) <- elaborate False (SET :>: iI)
>       (d :=>: dv) <- elaborate False (ARR iIv (IDESC iIv) :>: d)
>       (i :=>: iv) <- elaborate False (iIv :>: i)
>       lastIsIndex <- withNSupply (equal (SET :>: (iv,N (P (last xs)))))
>       guard lastIsIndex
>       -- should check i doesn't appear in d (fairly safe it's not in iI :))
>       return (IMU (Just lt) iI d i :=>: IMU (Just lv) iIv dv iv)