module Main exposing (main)

import Browser
import Html exposing (Html, button, div, text)
import Html.Events exposing (onClick)
import Html.Attributes exposing (class)

type alias Model =
  {}

type alias Msg = ()

main : Program () Model Msg
main =
  Browser.element
    { init = \_ -> ({}, Cmd.none)
    , update = \_  model -> (model, Cmd.none)
    , subscriptions = \_ -> Sub.none
    , view = view
    }

view : Model -> Html Msg
view model =
  let
    sequent =
      ( [ Impl (Atom "A") (Atom "B")
        , Atom "A"
        ]
      , [ Atom "B"
        , Neg (Atom "C")
        , Atom "D"
        ]
      )
  in
  div []
    [ sequent
        |> sequentToString
        |> Html.text
    , Object sequent
        |> proofSearch testRules
        |> printProof
    ]

type Formula
  = Atom String
  | Neg Formula
  | Conj Formula Formula
  | Disj Formula Formula
  | Impl Formula Formula

formulaToString f =
  case f of
     Atom s -> s
     Neg a -> "¬ " ++ formulaToString a
     Conj a b -> formulaToString a ++ " ∧ " ++ formulaToString b
     Disj a b -> formulaToString a ++ " ∨ " ++ formulaToString b
     Impl a b -> formulaToString a ++ " → " ++ formulaToString b

isAtom f =
  case f of
     Atom _ -> True
     _ -> False

isConj f =
  case f of
     Conj _ _ -> True
     _ -> False

isDisj f =
  case f of
    Disj _ _ -> True
    _ -> False

isImpl f =
  case f of
    Impl _ _ -> True
    _ -> False

isNeg f =
  case f of
    Neg _ -> True
    _ -> False

type alias Sequent = (List Formula, List Formula)

sequentToString s =
  let
    cedentToString c =
      c
      |> List.map formulaToString
      |> List.intersperse ", "
      |> List.foldr (++) ""
    
    first = cedentToString (Tuple.first s)
    second = cedentToString (Tuple.second s)
  in
  first ++ " ⊢ " ++ second

{-

Proofs.

Proofs come in a number of types:
 - Arrow: An arrow links a sequent to a proof by a rule.
 - Product: A product of two sequents, used for two simultaneous premises.
 - Sum: Another product of two sequents, used for two potential premises.
 - FibredSum: Fibred sum over potential permutations of lists of contexts in potential assumptions.
 - FibredProduct: Fibred product over potential permutations of list contexts in assumptions.

-}
type Proof
  = Arrow Sequent String Proof
  | Product Proof Proof
  | Sum Proof Proof
  | FibredSum (List Proof)
  | FibredProduct (List Proof)
  | Object Sequent

type Rule = Rule String (Sequent -> Maybe Proof)

ruleName : Rule -> String
ruleName rule =
  case rule of
    Rule s _ -> s

ruleFunction : Rule -> (Sequent -> Maybe Proof)
ruleFunction rule =
  case rule of
    Rule _ r -> r

extractFirst : (Formula -> Bool) -> List Formula -> Maybe (Formula, List Formula)
extractFirst condition cedent =
  cedent
    |> List.filter condition
    |> List.head
    |> Maybe.map (\match -> (match, List.filter ((/=) match) cedent))

testRules : List Rule
testRules =
  [ Rule "LNot" 
      <| \(ant, suc) ->
        case extractFirst isNeg ant of
          Just (Neg f, rest) ->
              Just (Object (rest, List.append suc [f]))
          _ -> Nothing
  , Rule "RNot"
      <| \(ant, suc) ->
        case extractFirst isNeg suc of
          Just (Neg f, rest) ->
            Just (Object (List.append ant [f], rest))
          _ -> Nothing
  ]

proofSearch : List Rule -> Proof -> Proof
proofSearch rules proof =
  let
    firstResult s =
      rules
        |> List.filterMap (\(Rule string rule) -> Maybe.map (\p -> (string, p)) (rule s))
        |> List.head
  in
  case proof of
    Object sequent ->
      case firstResult sequent of
        Just (ident, p) ->
          Arrow sequent ident (proofSearch rules p)
        Nothing -> Object sequent
    FibredSum list ->
      FibredSum (List.map (proofSearch rules) list)
    FibredProduct list ->
      FibredProduct (List.map (proofSearch rules) list)
    Product p q ->
      Product (proofSearch rules p) (proofSearch rules q)
    Sum p q ->
      Sum (proofSearch rules p) (proofSearch rules q)
    Arrow p i q ->
      Arrow p i (proofSearch rules q)

printProof : Proof -> Html Msg
printProof proof =
  case proof of
     Object sequent -> div [] [ text <| sequentToString sequent ]
     Arrow a r b -> div [] [ div [] [ text <| sequentToString a ], div [] [ text r ], div [] [ printProof b] ]
     FibredSum _ -> div [] []
     FibredProduct _ -> div [] []
     Sum _ _ -> div [] []
     Product _ _ -> div [] []