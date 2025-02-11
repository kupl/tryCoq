let list =
  [ Ir.TypeDecl
      ( "list"
      , [ Tany ]
      , [ Constructor "nil", []
        ; Constructor "Cons", [ Tany; Talgebraic ("list", [ Tany ]) ]
        ] )
  ; Ir.Rec
      ( "@"
      , [ "l1"; "l2" ]
      , { desc =
            Match
              ( { desc = Var "l1"; typ = Talgebraic ("list", [ Tany ]) }
              , [ Case
                    ( Pat_Constr ("[]", [])
                    , { desc = Var "l2"; typ = Talgebraic ("list", [ Tany ]) } )
                ; Case
                    ( Pat_Constr ("::", [ Pat_Tuple [ Pat_Var "hd"; Pat_Var "tl" ] ])
                    , { desc =
                          Call
                            ( "::"
                            , [ { desc =
                                    Tuple
                                      [ { desc = Var "hd"; typ = Tany }
                                      ; { desc =
                                            Call
                                              ( "@"
                                              , [ { desc = Var "tl"
                                                  ; typ = Talgebraic ("list", [ Tany ])
                                                  }
                                                ; { desc = Var "l2"
                                                  ; typ = Talgebraic ("list", [ Tany ])
                                                  }
                                                ] )
                                        ; typ = Talgebraic ("list", [ Tany ])
                                        }
                                      ]
                                ; typ = Ttuple [ Tany; Talgebraic ("list", [ Tany ]) ]
                                }
                              ] )
                      ; typ = Talgebraic ("list", [ Tany ])
                      } )
                ] )
        ; typ = Talgebraic ("list", [ Tany ])
        } )
  ]
;;

let bool =
  [ Ir.TypeDecl ("bool", [], [ Constructor "true", []; Constructor "false", [] ])
  ; Ir.NonRec
      ( "not"
      , [ "b" ]
      , { desc =
            Match
              ( { desc = Var "b"; typ = Talgebraic ("bool", []) }
              , [ Case
                    ( Pat_Constr ("true", [])
                    , { desc = Call ("false", []); typ = Talgebraic ("bool", []) } )
                ; Case
                    ( Pat_Constr ("false", [])
                    , { desc = Call ("true", []); typ = Talgebraic ("bool", []) } )
                ] )
        ; typ = Talgebraic ("bool", [])
        } )
  ]
;;

let initial_env = [ list; bool ]
