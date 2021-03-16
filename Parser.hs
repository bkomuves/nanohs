
-- | Parsing

{-# LANGUAGE NoImplicitPrelude, MagicHash #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings, OverloadedLists #-}

module Parser where

--------------------------------------------------------------------------------

import Prelude ( Int , Char , Eq , Show )
import PrimGHC

--------------------------------------------------------------------------------

import Base
import Types
import Syntax

{-% include "Base.hs"   %-}
{-% include "Types.hs"  %-}
{-% include "Syntax.hs" %-}

--------------------------------------------------------------------------------
-- * Parsing

mbVar  :: Token -> Maybe Name
mbLit  :: Token -> Maybe Literal
mbSpec :: Token -> Maybe Special

mbVar  tok = case tok of { VarTok  v -> Just v ; _ -> Nothing }
mbLit  tok = case tok of { LitTok  l -> Just l ; _ -> Nothing }
mbSpec tok = case tok of { SpecTok s -> Just s ; _ -> Nothing }

mbVarL :: Token -> Maybe Name
mbVarU :: Token -> Maybe Name
mbVarL tok = case mbVar tok of { Just str -> ifte (isLower_ (head str)) (Just str) Nothing }  
mbVarU tok = case mbVar tok of { Just str -> ifte (isUpper  (head str)) (Just str) Nothing }  

mbStrLit  :: Token -> Maybe String
mbStrLit tok = case mbLit tok of { Nothing -> Nothing ; Just lit -> 
  case lit of { StrL s -> Just s ; _ -> Nothing } }

isNotWhite :: Token -> Bool
isNotWhite tok = case tok of { WhiteTok -> False ; _ -> True }

locatedL :: Parser tok a -> Parser tok (Located a)
locatedL parser = pbind getFn     (\fname ->
                  pbind getSrcPos (\pos1  ->
                  pbind parser    (\what  ->
                  pbind getSrcPos (\pos2  -> preturn (Located (Loc fname pos1 pos2) what)))))

type LList a = List (Located a)
type LString = LList Char

addLocations :: FilePath -> String -> LString
addLocations fname text = go startSrcPos text where { go pos str = case str of { Nil -> Nil
  ; Cons x xs -> let { pos' = nextSrcPos x pos } in Cons (Located (Loc fname pos pos') x) (go pos' xs) } }

--------------------------------------------------------------------------------
-- ** Parser combinators

data ParseResult tok a
  = ParseOk a SrcPos (LList tok)
  | ParseErr  SrcPos
  deriving Show

type Parser tok a = FilePath -> SrcPos -> LList tok -> ParseResult tok a

runParser' :: FilePath -> Parser tok a -> LList tok -> ParseResult tok a
runParser' fname parser input = case input of { Nil -> error "empty input"
  ; Cons locx _ -> parser fname (locatedStart locx) input }

runParser :: FilePath -> Parser tok a -> LList tok -> Either String a
runParser fname p input = case runParser' fname p input of
  { ParseOk x pos rest -> case rest of
    { Nil -> Right x
    ; Cons _ _ ->   Left (append "unexpected extra token at " (showSrcPos' fname pos)) }
  ; ParseErr pos -> Left (append "parse error at "            (showSrcPos' fname pos)) }

runParser_ :: FilePath -> Parser tok a -> LList tok -> a
runParser_ fname p input = case runParser fname p input of { Right y -> y ; Left msg -> error msg }

preturn :: a -> Parser tok a
preturn x fn pos str = ParseOk x pos str

pfail :: Parser tok a
pfail fn pos str = ParseErr pos

pfmap :: (a -> b) -> Parser tok a -> Parser tok b
pfmap f p = \fn pos str -> case p fn pos str of
  { ParseOk x pos' str' -> ParseOk (f x) pos' str'
  ; ParseErr  pos'      -> ParseErr pos' }

preplace :: b -> Parser tok a -> Parser tok b
preplace x = pfmap (const x)

pbind :: Parser tok a -> (a -> Parser tok b) -> Parser tok b
pbind p u = \fn pos str -> case p fn pos str of
  { ParseOk x pos' str' -> u x fn pos' str'
  ; ParseErr  pos'      -> ParseErr pos' }

pseq  :: Parser tok a -> Parser tok b -> Parser tok b
pseq  p q = pbind p (\_ -> q)

ppost :: Parser tok a -> Parser tok b -> Parser tok a
ppost p q = pbind p (\x -> pbind q (\_ -> preturn x))

getFn :: Parser tok FilePath
getFn = \fn pos str -> ParseOk fn pos str

getSrcPos :: Parser tok SrcPos
getSrcPos = \fn pos str -> ParseOk pos pos str

alternative :: Parser tok a -> Parser tok a -> Parser tok a
alternative p q = \fn pos str -> case p fn pos str of
  { ParseOk x pos' str' -> ParseOk x pos' str'
  ; ParseErr _          -> q fn pos str }

choice :: List (Parser tok a) -> Parser tok a
choice list = case list of { Nil -> pfail ; Cons p ps -> alternative p (choice ps) }

optional :: Parser tok a -> Parser tok (Maybe a)
optional p = \fn pos str -> case p fn pos str of
  { ParseOk x pos' str' -> ParseOk (Just x) pos' str'
  ; ParseErr  _pos'     -> ParseOk Nothing  pos  str  }

option :: a -> Parser tok a -> Parser tok a
option x0 p = \fn pos str -> case p fn pos str of
  { ParseOk x pos' str'  -> ParseOk x  pos' str'
  ; ParseErr  _pos'      -> ParseOk x0 pos  str  }

many :: Parser tok a -> Parser tok (List a)
many p = pbind (optional p) (\mb -> case mb of
  { Nothing -> preturn Nil ; Just x -> pbind (many p) (\xs -> preturn (Cons x xs)) })

many1 :: Parser tok a -> Parser tok (List a)
many1 p = pbind p        (\x ->
          pbind (many p) (\xs -> preturn (Cons x xs)))

manyTill :: Parser tok end -> Parser tok a -> Parser tok (List a)
manyTill end p = go where { go = alternative (preplace Nil end)
  (pbind p (\x -> pbind go (\xs -> preturn (Cons x xs)))) }

sepEndBy :: Parser tok sep -> Parser tok end -> Parser tok a -> Parser tok (List a)
sepEndBy sep end p = alternative (preplace Nil end) (sepEndBy1 sep end p)

sepEndBy1 :: Parser tok sep -> Parser tok end -> Parser tok a -> Parser tok (List a)
sepEndBy1 sep end p = pbind p (\x -> alternative
  (preplace (Cons x Nil) end)
  (pseq sep (pbind (sepEndBy sep end p) (\xs -> preturn (Cons x xs)))))

accept :: (tok -> Maybe a) -> Parser tok a
accept f fn pos toks = case toks of
  { Nil -> ParseErr pos
  ; Cons locx xs -> case locx of { Located loc x -> case f x of
    { Just y    -> ParseOk y (locEnd loc) xs
    ; Nothing   -> ParseErr pos } } }

satisfy :: (tok -> Bool) -> Parser tok tok
satisfy f fn pos toks = case toks of
  { Nil -> ParseErr pos
  ; Cons locx xs -> case locx of { Located loc x -> case f x of
    { True  -> ParseOk x (locEnd loc) xs
    ; False -> ParseErr pos } } }

anyToken :: Parser tok tok
anyToken = satisfy (\_ -> True) 

token :: Eq tok => tok -> Parser tok tok
token t = satisfy (geq t) 

tokens :: Eq tok => List tok -> Parser tok (List tok)
tokens toks = case toks of { Nil -> preturn Nil ; Cons t ts ->
  pbind (token t) (\x -> pbind (tokens ts) (\xs -> preturn (Cons x xs))) }

charToken :: Char -> Parser Char Char
charToken t = satisfy (ceq t) 

charTokens :: String -> Parser Char String
charTokens toks = case toks of { Nil -> preturn Nil ; Cons t ts ->
  pbind (charToken t) (\x -> pbind (charTokens ts) (\xs -> preturn (Cons x xs))) }

oneOf :: Eq tok => List tok -> Parser tok tok
oneOf list = satisfy (\x -> elem x list)

noneOf :: Eq tok => List tok -> Parser tok tok
noneOf list = satisfy (\x -> not (elem x list))

charOneOf :: List Char -> Parser Char Char
charOneOf list = satisfy (\x -> charElem x list)

charNoneOf :: List Char -> Parser Char Char
charNoneOf list = satisfy (\x -> not (charElem x list))

eof :: Parser tok Unit
eof fn pos str = case str of { Nil -> ParseOk Unit pos str ; Cons _ _ -> ParseErr pos }

--------------------------------------------------------------------------------
-- * Parsing the pseudo-Haskell syntax
-- ** Lexer

type Lexer a = Parser Char a

digitL    = satisfy isDigit
lowerL    = satisfy isLower
upperL    = satisfy isUpper
alphaL    = satisfy isAlpha
_alphaL   = satisfy (\ch -> or (ceq ch '_') (isAlpha ch))
alphaNumL = satisfy isAlphaNum

spaces0 :: Lexer Int
spaces0 = pfmap length (many (charToken ' '))

spaces1 :: Lexer Int
spaces1 = pfmap length (many1 (charToken ' '))

digitsL :: Lexer String
digitsL = many1 digitL

natL :: Lexer Int
natL = pbind digitsL (\xs -> case readNat xs of { Just n -> preturn n ; Nothing -> pfail })

intL :: Lexer Int
intL = pbind (optional (charToken '-'))
  (\mb -> case mb of { Nothing -> natL ; Just _ -> pfmap negate natL })

charLiteralL :: Lexer Char
charLiteralL =
  pbind (charToken singleQuoteC) (\_ ->
  pbind (anyToken              ) (\c ->
  pbind (charToken singleQuoteC) (\_ -> preturn c)))

stringLiteralL :: Lexer String
stringLiteralL =
  pbind (charToken doubleQuoteC)                 (\_  ->
  pbind (many (satisfy (cneq doubleQuoteC)))     (\xs ->
  pbind (charToken doubleQuoteC)                 (\_  -> preturn xs)))

identifierL :: Lexer Name
identifierL = pbind _alphaL                                          (\x  ->
              pbind (many (alternative alphaNumL (charOneOf "_'#"))) (\xs ->
              preturn (Cons x xs)))

literalL :: Lexer Literal
literalL = choice
  [ pfmap IntL intL
  , pfmap ChrL charLiteralL
  , pfmap StrL stringLiteralL ]

specialL :: Lexer Special
specialL = choice
  [ preplace LParen    (charToken  '(' )
  , preplace RParen    (charToken  ')' )
  , preplace LBrace    (charToken  '{' )
  , preplace RBrace    (charToken  '}' )
  , preplace LBracket  (charToken  '[' )
  , preplace RBracket  (charToken  ']' )
  , preplace Arrow     (charTokens "->")
  , preplace DArrow    (charTokens "=>")
  , preplace HasType   (charTokens "::")
  , preplace Comma     (charToken  ',' )
  , preplace Semicolon (charToken  ';' )
  , preplace EqualSign (charToken  '=' )
  , preplace Pipe      (charToken  '|' )
  , preplace Lambda    (charToken  backslashC)
  , preplace Dot       (charToken  '.' )
  ]

lexemeL :: Lexer Token
lexemeL = choice
  [ pfmap    LitTok   literalL
  , pfmap    SpecTok  specialL
  , pfmap    VarTok   identifierL
  , preplace WhiteTok spaces1
  ]

-- | 0x0A, or 0x0D, or 0x0D,0x0A.
eol_ :: Lexer Unit
eol_ = alternative linux windows where
  { linux   = preplace Unit (charToken newlineC)
  ; windows = preplace Unit (pseq (charToken carriageReturnC) (optional (charToken newlineC))) }

eol :: Lexer Unit
eol = alternative eol_ eof

eolIndent :: Lexer Int
eolIndent = alternative (pseq eol_ spaces0) (preplace 0 eof)

-- | with EOL
commentL :: Lexer String
commentL = ppost commentL' eol

-- | without EOL
commentL' :: Lexer String
commentL' = choice [ comment1 , comment2 ] where
  { comment1 = pseq (charTokens "--" ) (many (charNoneOf [newlineC,carriageReturnC]))
  ; comment2 = pseq (charTokens "{-#") (many (charNoneOf [newlineC,carriageReturnC]))
  }

-- | We need to hide some stuff (for example @include@-s) from GHC
nanoPragmaL :: Lexer Block
nanoPragmaL = 
  pbind (charTokens "{-%")                                         (\_  -> 
  pbind (many1 (locatedL lexemeL))                                 (\ln -> 
  pbind (charTokens "%-}")                                         (\_  ->
  pbind (ppost (many (charNoneOf [newlineC,carriageReturnC])) eol) (\_  -> preturn ln))))

-- | Note: this accepts "eof"!
emptyLineL :: Lexer Unit
emptyLineL = pseq spaces0 eol

type Block = List LToken

-- | Parser a line and all following indented lines
blockL :: Lexer Block
blockL = worker1 where
  { line    = alternative comment (many1 (locatedL lexemeL))
  ; comment = pseq commentL' (preturn Nil)
  ; worker  = pbind eolIndent (\k -> ifte (gt k 0) (option Nil worker1) (preturn Nil))
  ; worker1 = pbind line      (\ls1 -> pbind worker (\ls2 -> preturn (append ls1 ls2)))
  }

blockOrCommentL :: Lexer (Maybe Block)
blockOrCommentL = choice
  [ preplace Nothing commentL
  , preplace Nothing emptyLineL
  , pfmap    Just    nanoPragmaL
  , pfmap    Just    blockL
  ]

programL :: Lexer (List Block)
programL = pfmap catMaybes (manyTill eof blockOrCommentL)

lexer :: FilePath -> String -> List Block
lexer fname input = runParser_ fname programL (addLocations fname input)

--------------------------------------------------------------------------------
-- ** The parser

type Parse a = Parser Token a

parseTopLevelBlock :: FilePath -> Block -> TopLevel
parseTopLevelBlock fname tokens = runParser_ fname topLevelP (filterWhite tokens)

filterWhite :: Block -> Block
filterWhite = filter cond where { cond ltok = isNotWhite (located ltok) }

keywords :: List String
keywords = [ "where" , "case" , "of" , "let" , "let_" , "in" , "module" , "import" , "include" , "data" , "type" ]

isKeyword :: String -> Bool
isKeyword str = elem str keywords

topLevelP :: Parse TopLevel
topLevelP = choice
  [ tyAliasP
  , dataDeclP
  , importP
  , includeP
  , moduleP
  , tyDeclP
  , pfmap TopDefin definP
  ]

tyDeclP :: Parse TopLevel
tyDeclP = pbind  varP            (\name ->
          pbind (specP HasType ) (\_    ->
          pbind (many1 anyToken) (\toks -> preturn (TopTyDecl name toks) )))

dataDeclP :: Parse TopLevel
dataDeclP = pbind (keywordP "data") (\_ ->
            pbind (many1 anyToken ) (\toks -> preturn (TopDataDecl toks) ))

tyAliasP :: Parse TopLevel
tyAliasP = pbind (keywordP "type") (\_ ->
           pbind (many1 anyToken ) (\toks -> preturn (TopTyAlias toks) ))

-- haskell import
importP :: Parse TopLevel
importP = pbind (keywordP "import") (\_ ->
          pbind (many1 anyToken   ) (\toks -> preturn (TopImport toks) ))

-- our C-style include
includeP :: Parse TopLevel
includeP = pbind (keywordP "include") (\_ ->
           pbind (accept mbStrLit   ) (\fname -> preturn (TopInclude fname) ))

moduleP :: Parse TopLevel
moduleP = pbind (keywordP "module") (\_ ->
          pbind (many1 anyToken   ) (\toks -> preturn (TopModule toks) ))

definP :: Parse DefinE
definP f p t = 
  pbind varP              (\name ->
  pbind (many varP)       (\args ->
  pbind (specP EqualSign) (\_    ->
  pbind exprP             (\body -> preturn (Defin name (lamsE args body)) ))))  f p t 

exprP :: Parse Expr
exprP f p t = 
  pbind nakedExprP             (\expr ->
  pbind (optional whereBlockP) (\mb   ->
  preturn (case mb of { Nothing -> expr ; Just defs -> RecE defs expr } )))  f p t 

whereBlockP :: Parse (List DefinE)
whereBlockP f p t = pbind (keywordP "where") (\_ -> blockP) f p t 

-- | Here \"naked\" means without a where block
nakedExprP :: Parse Expr
nakedExprP f p t = choice
  [ lamExprP
  , pfmap listAppsE (many1 atomP)
  ]  f p t 

-- | We need an explicit eta-expansion here so that it doesn't loop in GHCi
-- (and probably also itself)
atomP :: Parse Expr
atomP f p t = choice
  [ inParensP exprP
  , pfmap LitE  literalP
  , pfmap ListE listExprP
  , caseExprP
  , letsExprP , letRecExprP
  , pfmap VarE (locatedL varP)
  ] f p t 

specP :: Special -> Parse Special
specP spec = preplace spec (token (SpecTok spec))

literalP :: Parse Literal
literalP = accept mbLit

-- capitalIdentP :: Parse Name
-- capitalIdentP = accept mbVarU

identP :: Parse Name
identP = accept mbVar

-- | This does not accepts they keywords, but accepts constructors
varP :: Parse Name
varP = pbind identP (\v -> ifte (isKeyword v) pfail (preturn v))

-- | This only accept uppercase identifiers
conP :: Parse Name
conP = accept mbVarU

keywordP :: String -> Parse String
keywordP word = pbind identP (\v -> ifte (geq v word) (preturn word) pfail)

inParensP :: Parse a -> Parse a
inParensP p = pbind (specP LParen) (\_ ->
              pbind p              (\x ->
              pbind (specP RParen) (\_ -> preturn x)))

listExprP  :: Parse (List Expr   )
tupleExprP :: Parse (List Expr   )
blockP     :: Parse (List DefinE )
branchesP  :: Parse (List BranchE)

listExprP  f p t = pbind (specP LBracket) (\_ -> sepEndBy (specP Comma    ) (specP RBracket) exprP  ) f p t
tupleExprP f p t = pbind (specP LParen  ) (\_ -> sepEndBy (specP Comma    ) (specP RParen  ) exprP  ) f p t
blockP     f p t = pbind (specP LBrace  ) (\_ -> sepEndBy (specP Semicolon) (specP RBrace  ) definP ) f p t
branchesP  f p t = pbind (specP LBrace  ) (\_ -> sepEndBy (specP Semicolon) (specP RBrace  ) branchP) f p t

patternP :: Parse Pattern
patternP f p t = naked f p t where
  { naked f p t = choice [ wild , var , inParensP patternP , apps ] f p t
  ; safe  f p t = choice [ wild , var , inParensP patternP , con  ] f p t
  ; wild  = pbind (keywordP "_" ) (\_    -> preturn  WildP  )
  ; var   = pbind (accept mbVarL) (\v    -> preturn (VarP v))
  ; con   = pbind  conP           (\con  -> preturn (AppP con Nil))
  ; apps  = pbind  conP           (\con  ->
            pbind (many safe    ) (\args -> preturn (AppP con args)))
  }  

branchP :: Parse BranchE
branchP f p t = alternative defaultBranchP branchP' f p t

branchP' :: Parse BranchE
branchP' f p t = 
  pbind conP          (\con  ->
  pbind (many varP  ) (\args ->
  pbind (specP Arrow) (\_    ->
  pbind (exprP      ) (\body -> preturn (BranchE con args body))))) f p t 

defaultBranchP :: Parse BranchE
defaultBranchP f p t 
  = pbind (keywordP "_") (\_    ->
    pbind (specP Arrow ) (\_    ->
    pbind (exprP       ) (\body -> preturn (DefaultE body)))) f p t 

lamExprP :: Parse Expr
lamExprP f p t  =
  pbind (specP Lambda) (\_    ->
  pbind (many1 varP  ) (\args ->
  pbind (specP Arrow ) (\_    ->
  pbind exprP          (\body -> preturn (lamsE args body))))) f p t 

letExprP' :: (List DefinE -> Expr -> Expr) -> String -> Parse Expr
letExprP' con letkw = pbind (keywordP letkw) (\_    ->
                  pbind (blockP        ) (\defs ->
                  pbind (keywordP "in" ) (\_    ->
                  pbind (exprP         ) (\expr -> preturn (con defs expr)))))

-- | Non-recursive let
letsExprP :: Parse Expr
letsExprP f p t = letExprP' LetE "let_" f p t 

-- | Recursive let
letRecExprP :: Parse Expr
letRecExprP f p t = letExprP' RecE "let" f p t 

caseExprP :: Parse Expr
caseExprP f p t  = 
  pbind (keywordP "case") (\_     ->
  pbind (locatedL exprP ) (\lexpr ->
  pbind (keywordP "of"  ) (\_     ->
  pbind (branchesP      ) (\brs   -> preturn (CaseE lexpr brs))))) f p t 

--------------------------------------------------------------------------------
