 {-# OPTIONS -fallow-overlapping-instances -fallow-undecidable-instances  -fno-monomorphism-restriction #-}

module DLParser where





import Control.Monad(liftM)
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language
import Text.ParserCombinators.Parsec.Expr
import qualified Text.ParserCombinators.Parsec.Token as Token


import DL
import DLPrint
import Causal
import InterpreterLib.Terms.Arith
import InterpreterLib.Terms.LambdaTerm
import InterpreterLib.Terms.IfTerm
import InterpreterLib.Functors






ldef = haskellStyle { reservedNames = ["let", "in", "and","if","then","else","true","false"],
                      reservedOpNames = ["+","-","*","/", "@"]}
lexer = Token.makeTokenParser ldef




symbol = Token.symbol lexer
integer = Token.integer lexer 
operator = Token.operator lexer
parens = Token.parens lexer
semi = Token.semi lexer
identifier = Token.identifier lexer
whiteSpace = Token.whiteSpace lexer
decimal = Token.decimal lexer
reservedOp = Token.reservedOp lexer
reserved = Token.reserved lexer
natural = Token.natural lexer
semiSep1 = Token.semiSep1 lexer



table   = [[op "*" makeMult AssocLeft, op "/"  makeDiv AssocLeft]          
          ,[op "+" makeAdd AssocLeft, op "-" makeSub AssocLeft]
          ,[op "==" makeNumEq AssocRight]
          ,[op "@" makeFBy AssocRight]]
  where op s f assoc = 
          Infix (do{ symbol s; return (\a1 a2 -> f a1 a2);}) assoc




expr = constant    <|>
       variable <|>
       ifExpr <|>
       parens term
-- term = chainl1 funapp op 

term = buildExpressionParser table funapp



funapp :: GenParser Char st TermLang
funapp = do exprs <- chainl1 lexpr comb
            case exprs of
              [x] -> return x
              (f:args) -> case (prjF (out f)) of 
                               Just (VarTerm x) -> return $ foldl makeApp' f args
                               Nothing -> fail "Calling a non-named function"

    where lexpr = do { e <- expr; return [e]}
          comb = do { return (++)}
          makeApp' = mkMkApp (undefined :: ())

-- mkMkApp :: SubFunctor (LamdaTerm a) t => a -> t -> t -> t
mkMkApp (_ :: ty) x y= inn $ injF $ (App :: t -> t -> LambdaTerm ty t) x y

 


{-
-- funapp :: GenParser Char st Lang
funapp = do exprs <- chainl1 lexpr comb
            case exprs of 
              (f:args) -> return $ foldl (appGen (undefined :: ())) f args
              _ -> fail "Trying to apply a function which is a non-variable"
   where lexpr = do { e <- expr; return [e]}
         comb = do { return (++)}
-}




variable = liftM makeVarTerm identifier <?> "cannot parse variable"




constant = (liftM (makeNum . fromInteger) natural)  <|>
           boolConstant <?> "Cannot parse constant"

boolConstant = do { reserved "true"; return makeTrueTerm } <|>
               do {reserved "false"; return makeFalseTerm}



binding = do n <- identifier
             reservedOp "="
             e <- term
             return (n,e)

bindings = semiSep1 binding




ifExpr = do reserved "if"
            pred <- term
            reserved "then"
            thenClause <- term
            reserved "else"
            elseClause <- term
            return $ makeIfTerm pred thenClause elseClause





program = sepBy1 declaration (reserved "and")

declaration = do n <- identifier
                 args <- many identifier
                 reservedOp "="
                 body <- term
                 return (n,foldr (\v b -> makeLam v () b) body args)





parseExpr parser str = runParser  parser 0 "Test Expression" str 
parseSAFL = parseExpr program




parseLang :: String -> IO [(String,TermLang)]
parseLang fname = do str <- readFile fname
                     case parseSAFL str of
                      Left err -> fail (show err)
                      Right x -> do mapM printing x
                                    return x
  where printing (n,v) = putStrLn $ n ++ " = " ++ (show $ printAlg v)


