module CaseWhen
    ( caseWhenLists, caseWhenTuples) where

---------------------------------------------------------------------------
-- caseWhenList searchValue [v1,v2] [r1,r2] notFoundValue
---------------------------------------------------------------------------
-- caseWhenTuples searchValue [(v1,r1),(v2,r2)] notFoundValue
---------------------------------------------------------------------------
-- switch(searchValue) {
--     case v1: {
--        return r1; 
--        break;
--     }
--     case v2: {
--        return r1; 
--        break;
--     }
--     otherwise: {
--         return notFoundValue
--     }
-- }
-- 
---------------------------------------------------------------------------
caseWhenLists search []          _          notFound = notFound
caseWhenLists search (v:values) (r:returns) notFound = if ( search == v )
                        then r
                        else caseWhenLists search values returns notFound


caseWhenTuples search []                  notFound = notFound
caseWhenTuples search ((value,result):xs) notFound = if ( search == value )
                        then result
                        else caseWhenTuples search xs notFound
