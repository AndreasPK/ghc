
import GHC.Word
import GHC.Int

import System.Environment

w8s  = [0, 1, maxBound] :: [Word8]
w16s = [0, 1, maxBound] :: [Word16]
w32s = [0, 1, maxBound] :: [Word32]
w64s = [0, 1, maxBound] :: [Word64]
ws   = [0, 1, maxBound] :: [Word]

i8s  = [minBound, -1, 0, 1, maxBound] :: [Int8]
i16s = [minBound, -1, 0, 1, maxBound] :: [Int16]
i32s = [minBound, -1, 0, 1, maxBound] :: [Int32]
i64s = [minBound, -1, 0, 1, maxBound] :: [Int64]
is   = [minBound, -1, 0, 1, maxBound] :: [Int]

main :: IO ()
main = do
    putStrLn "min calls"

    print $ (\vals -> map (\f -> map f vals) (map min vals)) w8s
    print $ (\vals -> map (\f -> map f vals) (map min vals)) w16s
    print $ (\vals -> map (\f -> map f vals) (map min vals)) w32s
    print $ (\vals -> map (\f -> map f vals) (map min vals)) w64s
    print $ (\vals -> map (\f -> map f vals) (map min vals)) ws
    print $ (\vals -> map (\f -> map f vals) (map min vals)) i8s
    print $ (\vals -> map (\f -> map f vals) (map min vals)) i16s
    print $ (\vals -> map (\f -> map f vals) (map min vals)) i32s
    print $ (\vals -> map (\f -> map f vals) (map min vals)) i64s
    print $ (\vals -> map (\f -> map f vals) (map min vals)) is

    putStrLn "max calls"

    print $ (\vals -> map (\f -> map f vals) (map max vals)) w8s
    print $ (\vals -> map (\f -> map f vals) (map max vals)) w16s
    print $ (\vals -> map (\f -> map f vals) (map max vals)) w32s
    print $ (\vals -> map (\f -> map f vals) (map max vals)) w64s
    print $ (\vals -> map (\f -> map f vals) (map max vals)) ws
    print $ (\vals -> map (\f -> map f vals) (map max vals)) i8s
    print $ (\vals -> map (\f -> map f vals) (map max vals)) i16s
    print $ (\vals -> map (\f -> map f vals) (map max vals)) i32s
    print $ (\vals -> map (\f -> map f vals) (map max vals)) i64s
    print $ (\vals -> map (\f -> map f vals) (map max vals)) is

-- main = do
--     [x1,x2,x3,x4,x5,x6,x7,x8,x9,x10] <- map read <$> getArgs :: IO [Int32]
--     -- print $ x1+x2+x3+x4+x5+x6+x7+x8+x9+x10
--     let xs = [1 .. 10 :: Int]
--     print $ xs
--     print $ sum xs
--     -- print $ sum xs

