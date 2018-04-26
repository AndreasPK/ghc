module MatchTree where

import CoreSyn
import UniqSupply

cacheExpr :: MonadUnique m => CoreExpr -> m CoreExpr