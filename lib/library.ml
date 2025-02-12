let list =
  [ Ir.TypeDecl
      ( "list"
      , [ Tany ]
      , [ Constructor "[]", []
        ; Constructor "::", [ Tany; Talgebraic ("list", [ Tany ]) ]
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
                    ( Pat_Constr ("::", [ Pat_Var "hd"; Pat_Var "tl" ])
                    , { desc =
                          Call
                            ( "::"
                            , [ { desc = Var "hd"; typ = Tany }
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
                              ] )
                      ; typ = Talgebraic ("list", [ Tany ])
                      } )
                ] )
        ; typ = Talgebraic ("list", [ Tany ])
        } )
  ]
;;

let natural =
  [ Ir.TypeDecl
      ( "natural"
      , []
      , [ Constructor "Z", []; Constructor "S", [ Talgebraic ("natural", []) ] ] )
  ; Ir.Rec
      ( "add"
      , [ "n1"; "n2" ]
      , { desc =
            Match
              ( { desc = Var "n1"; typ = Talgebraic ("natural", []) }
              , [ Case
                    ( Pat_Constr ("Z", [])
                    , { desc = Var "n2"; typ = Talgebraic ("natural", []) } )
                ; Case
                    ( Pat_Constr ("S", [ Pat_Var "n1'" ])
                    , { desc =
                          Call
                            ( "S"
                            , [ { desc =
                                    Call
                                      ( "add"
                                      , [ { desc = Var "n1'"
                                          ; typ = Talgebraic ("natural", [])
                                          }
                                        ; { desc = Var "n2"
                                          ; typ = Talgebraic ("natural", [])
                                          }
                                        ] )
                                ; typ = Talgebraic ("natural", [])
                                }
                              ] )
                      ; typ = Talgebraic ("natural", [])
                      } )
                ] )
        ; typ = Talgebraic ("natural", [])
        } )
  ; Ir.Rec
      ( "sub"
      , [ "n1"; "n2" ]
      , { desc =
            Match
              ( { desc = Var "n2"; typ = Talgebraic ("natural", []) }
              , [ Case
                    ( Pat_Constr ("Z", [])
                    , { desc = Var "n1"; typ = Talgebraic ("natural", []) } )
                ; Case
                    ( Pat_Constr ("S", [ Pat_Var "n2'" ])
                    , { desc =
                          Match
                            ( { desc = Var "n1"; typ = Talgebraic ("natural", []) }
                            , [ Case
                                  ( Pat_Constr ("Z", [])
                                  , { desc = Call ("Z", [])
                                    ; typ = Talgebraic ("natural", [])
                                    } )
                              ; Case
                                  ( Pat_Constr ("S", [ Pat_Var "n1'" ])
                                  , { desc =
                                        Call
                                          ( "sub"
                                          , [ { desc = Var "n1'"
                                              ; typ = Talgebraic ("natural", [])
                                              }
                                            ; { desc = Var "n2'"
                                              ; typ = Talgebraic ("natural", [])
                                              }
                                            ] )
                                    ; typ = Talgebraic ("natural", [])
                                    } )
                              ] )
                      ; typ = Talgebraic ("natural", [])
                      } )
                ] )
        ; typ = Talgebraic ("natural", [])
        } )
  ; Ir.Rec
      ( "lt"
      , [ "n1"; "n2" ]
      , { desc =
            Match
              ( { desc = Var "n2"; typ = Talgebraic ("natural", []) }
              , [ Case
                    ( Pat_Constr ("Z", [])
                    , { desc = Call ("false", []); typ = Talgebraic ("bool", []) } )
                ; Case
                    ( Pat_Constr ("S", [ Pat_Var "n2'" ])
                    , { desc =
                          Match
                            ( { desc = Var "n1"; typ = Talgebraic ("natural", []) }
                            , [ Case
                                  ( Pat_Constr ("Z", [])
                                  , { desc = Call ("true", [])
                                    ; typ = Talgebraic ("bool", [])
                                    } )
                              ; Case
                                  ( Pat_Constr ("S", [ Pat_Var "n1'" ])
                                  , { desc =
                                        Call
                                          ( "lt"
                                          , [ { desc = Var "n1'"
                                              ; typ = Talgebraic ("natural", [])
                                              }
                                            ; { desc = Var "n2'"
                                              ; typ = Talgebraic ("natural", [])
                                              }
                                            ] )
                                    ; typ = Talgebraic ("bool", [])
                                    } )
                              ] )
                      ; typ = Talgebraic ("bool", [])
                      } )
                ] )
        ; typ = Talgebraic ("bool", [])
        } )
  ]
;;

let integer =
  [ Ir.TypeDecl
      ( "int"
      , []
      , [ Constructor "Zero", []
        ; Constructor "Pos", [ Talgebraic ("natural", []) ]
        ; Constructor "Neg", [ Talgebraic ("natural", []) ]
        ] )
  ; Ir.NonRec
      ( "+"
      , [ "i1"; "i2" ]
      , { desc =
            Match
              ( { desc = Var "i1"; typ = Talgebraic ("int", []) }
              , [ Case
                    ( Pat_Constr ("Zero", [])
                    , { desc = Var "i2"; typ = Talgebraic ("int", []) } )
                ; Case
                    ( Pat_Constr ("Pos", [ Pat_Var "n1" ])
                    , { desc =
                          Match
                            ( { desc = Var "i2"; typ = Talgebraic ("int", []) }
                            , [ Case
                                  ( Pat_Constr ("Zero", [])
                                  , { desc = Var "i1"; typ = Talgebraic ("int", []) } )
                              ; Case
                                  ( Pat_Constr ("Pos", [ Pat_Var "n2" ])
                                  , { desc =
                                        Call
                                          ( "Pos"
                                          , [ { desc =
                                                  Call
                                                    ( "add"
                                                    , [ { desc = Var "n1"
                                                        ; typ = Talgebraic ("natural", [])
                                                        }
                                                      ; { desc = Var "n2"
                                                        ; typ = Talgebraic ("natural", [])
                                                        }
                                                      ] )
                                              ; typ = Talgebraic ("natural", [])
                                              }
                                            ] )
                                    ; typ = Talgebraic ("int", [])
                                    } )
                              ; Case
                                  ( Pat_Constr ("Neg", [ Pat_Var "n2" ])
                                  , { desc =
                                        Match
                                          ( { desc =
                                                Call
                                                  ( "lt"
                                                  , [ { desc = Var "n1"
                                                      ; typ = Talgebraic ("natural", [])
                                                      }
                                                    ; { desc = Var "n2"
                                                      ; typ = Talgebraic ("natural", [])
                                                      }
                                                    ] )
                                            ; typ = Talgebraic ("bool", [])
                                            }
                                          , [ Case
                                                ( Pat_Constr ("true", [])
                                                , { desc =
                                                      Call
                                                        ( "Neg"
                                                        , [ { desc =
                                                                Call
                                                                  ( "sub"
                                                                  , [ { desc = Var "n2"
                                                                      ; typ =
                                                                          Talgebraic
                                                                            ("natural", [])
                                                                      }
                                                                    ; { desc = Var "n1"
                                                                      ; typ =
                                                                          Talgebraic
                                                                            ("natural", [])
                                                                      }
                                                                    ] )
                                                            ; typ =
                                                                Talgebraic ("natural", [])
                                                            }
                                                          ] )
                                                  ; typ = Talgebraic ("int", [])
                                                  } )
                                            ; Case
                                                ( Pat_Constr ("false", [])
                                                , { desc =
                                                      Call
                                                        ( "Pos"
                                                        , [ { desc =
                                                                Call
                                                                  ( "sub"
                                                                  , [ { desc = Var "n1"
                                                                      ; typ =
                                                                          Talgebraic
                                                                            ("natural", [])
                                                                      }
                                                                    ; { desc = Var "n2"
                                                                      ; typ =
                                                                          Talgebraic
                                                                            ("natural", [])
                                                                      }
                                                                    ] )
                                                            ; typ =
                                                                Talgebraic ("natural", [])
                                                            }
                                                          ] )
                                                  ; typ = Talgebraic ("int", [])
                                                  } )
                                            ] )
                                    ; typ = Talgebraic ("int", [])
                                    } )
                              ] )
                      ; typ = Talgebraic ("int", [])
                      } )
                ; Case
                    ( Pat_Constr ("Neg", [ Pat_Var "n1" ])
                    , { desc =
                          Match ({ desc = Var "i2"; typ = Talgebraic ("int", []) }, [])
                      ; typ = Talgebraic ("int", [])
                      } )
                ] )
        ; typ = Talgebraic ("int", [])
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
  ; Ir.NonRec
      ( "&&"
      , [ "b1"; "b2" ]
      , { desc =
            Match
              ( { desc = Var "b1"; typ = Talgebraic ("bool", []) }
              , [ Case
                    ( Pat_Constr ("true", [])
                    , { desc = Var "b2"; typ = Talgebraic ("bool", []) } )
                ; Case
                    ( Pat_Constr ("false", [])
                    , { desc = Call ("false", []); typ = Talgebraic ("bool", []) } )
                ] )
        ; typ = Talgebraic ("bool", [])
        } )
  ; Ir.NonRec
      ( "||"
      , [ "b1"; "b2" ]
      , { desc =
            Match
              ( { desc = Var "b1"; typ = Talgebraic ("bool", []) }
              , [ Case
                    ( Pat_Constr ("true", [])
                    , { desc = Call ("true", []); typ = Talgebraic ("bool", []) } )
                ; Case
                    ( Pat_Constr ("false", [])
                    , { desc = Var "b2"; typ = Talgebraic ("bool", []) } )
                ] )
        ; typ = Talgebraic ("bool", [])
        } )
  ]
;;

let initial_env = list @ natural @ integer @ bool
