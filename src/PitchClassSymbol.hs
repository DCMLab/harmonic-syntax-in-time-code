module PitchClassSymbol
    ( PitchClass(..)
    , PitchClassSymbol(..)
    , parsePCSym
    , transposePCSym
    , transposePCSymSeq
    -- , test
    ) where

import Text.Parsec
import qualified Data.Text as T

data PitchClass = PC0 | PC1 | PC2 | PC3 | PC4 | PC5 | PC6 | PC7 | PC8 | PC9 | PC10 | PC11
    deriving (Eq, Ord, Show)

instance Enum PitchClass where
    fromEnum a = case a of
        PC0  -> 0
        PC1  -> 1
        PC2  -> 2
        PC3  -> 3
        PC4  -> 4
        PC5  -> 5
        PC6  -> 6
        PC7  -> 7
        PC8  -> 8
        PC9  -> 9
        PC10 -> 10
        PC11 -> 11
    toEnum a = case a `mod` 12 of
        0  -> PC0
        1  -> PC1
        2  -> PC2
        3  -> PC3
        4  -> PC4
        5  -> PC5
        6  -> PC6
        7  -> PC7
        8  -> PC8
        9  -> PC9
        10 -> PC10
        11 -> PC11

instance Num PitchClass where
    a + b = toEnum $ fromEnum a + fromEnum b
    a - b = toEnum $ fromEnum a - fromEnum b
    a * b = toEnum $ fromEnum a * fromEnum b
    abs a = toEnum $ min (fromEnum a) (12 - fromEnum a)
    signum a
        | a == PC0   = PC0
        | a == abs a = PC1
        | otherwise  = PC11
    fromInteger = toEnum . fromInteger

accidential :: Parsec String st Int
accidential = do 
    accs <- many (oneOf "#b")
    return . sum . map toInt $ accs
    where toInt '#' =  1
          toInt 'b' = -1

naturalTone :: Parsec String st Int
naturalTone = do 
    letter <- oneOf "ABCDEFG"
    return $ case letter of
        'C' -> 0
        'D' -> 2
        'E' -> 4
        'F' -> 5
        'G' -> 7
        'A' -> 9
        'B' -> 11

pitchClass :: Parsec String st PitchClass
pitchClass = do
    t <- naturalTone
    a <- accidential
    return . toEnum $ t + a

data PitchClassSymbol = PCStart | PCSym PitchClass T.Text
    deriving (Eq, Ord)

instance Show PitchClassSymbol where
    show (PCSym pc form) = "[" ++ (show . fromEnum) pc ++ "]" ++ T.unpack form
    show PCStart = "PCStart"

pitchClassSymbol :: Parsec String st PitchClassSymbol
pitchClassSymbol = do 
    pc <- pitchClass
    form <- many anyChar
    return . PCSym pc . T.pack $ form

parsePCSym :: String -> PitchClassSymbol
parsePCSym sym = case parse pitchClassSymbol "" sym of
    Right pcSym -> pcSym
    Left _      -> error $ sym ++ " not parsable as pitch class symbol"

transposePCSym :: Int -> PitchClassSymbol -> PitchClassSymbol
transposePCSym i (PCSym pc form) = PCSym (pc + toEnum i) form
transposePCSym _ PCStart = PCStart

transposePCSymSeq :: [PitchClassSymbol] -> [PitchClassSymbol]
transposePCSymSeq cs = transposePCSym (negate . fromEnum . root . last $ cs) <$> cs where
    root (PCSym pc form) = pc

test = parsePCSym "F#m7"