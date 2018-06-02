module X86.Cond (
        Cond(..),
        condUnsigned,
        condToSigned,
        condToUnsigned,
        maybeFlipCond,
        maybeInvCond,
)

where

import GhcPrelude

data Cond
        = ALWAYS        -- What's really used? ToDo
        | EQQ
        | GE
        | GEU
        | GTT
        | GU
        | LE
        | LEU
        | LTT
        | LU
        | NE
        | NEG
        | POS
        | CARRY
        | OFLO
        | NOFLO
        | PARITY
        | NOTPARITY
        deriving Eq

condUnsigned :: Cond -> Bool
condUnsigned GU  = True
condUnsigned LU  = True
condUnsigned GEU = True
condUnsigned LEU = True
condUnsigned _   = False


condToSigned :: Cond -> Cond
condToSigned GU  = GTT
condToSigned LU  = LTT
condToSigned GEU = GE
condToSigned LEU = LE
condToSigned x   = x


condToUnsigned :: Cond -> Cond
condToUnsigned GTT = GU
condToUnsigned LTT = LU
condToUnsigned GE  = GEU
condToUnsigned LE  = LEU
condToUnsigned x   = x

-- | @maybeFlipCond c@ returns @Just c'@ if it is possible to flip the
-- arguments to the conditional @c@, and the new condition should be @c'@.
maybeFlipCond :: Cond -> Maybe Cond
maybeFlipCond cond  = case cond of
        EQQ   -> Just EQQ
        NE    -> Just NE
        LU    -> Just GU
        GU    -> Just LU
        LEU   -> Just GEU
        GEU   -> Just LEU
        LTT   -> Just GTT
        GTT   -> Just LTT
        LE    -> Just GE
        GE    -> Just LE
        _other -> Nothing

-- | @maybeInvCond c@ returns @Just c'@ if it is possible to invert the
-- condition itself.
-- In other words we can swap jcc l1; jmp l2 <-> j<invCC>; jmp l1
-- This DOES NOT imply inv . inv == id
-- TODO: Verify
maybeInvCond :: Cond -> Maybe Cond
maybeInvCond cond  = case cond of
        EQQ   -> Just NE
        GE    -> Just LTT
        GEU   -> Just LU
        GTT   -> Just LE
        GU    -> Just LEU
        LE    -> Just GTT
        LEU   -> Just GU
        LTT   -> Just GE
        LU    -> Just GEU
        NE    -> Just EQQ
        NEG   -> Just POS
        POS   -> Just NEG
        CARRY -> Just GEU
        OFLO  -> Just NOFLO
        NOFLO -> Just OFLO
        PARITY    -> Just NOTPARITY
        NOTPARITY -> Just PARITY
        ALWAYS -> Nothing
