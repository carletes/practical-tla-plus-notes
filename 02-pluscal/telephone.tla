----------------------------- MODULE telephone -----------------------------
EXTENDS Sequences, TLC

(*--algorithm telephone

variables
    to_send = <<1, 2, 3>>,
    received = <<>>,
    in_transit = {},
    can_send = TRUE;

begin
    while Len(received) /= 3 do
        if can_send /\ to_send /= <<>> then
            in_transit := in_transit \union {Head(to_send)};
            can_send := FALSE;
            to_send := Tail(to_send);
        end if;
        
        either
            with msg \in in_transit do
                received := Append(received, msg);
                in_transit := in_transit \ {msg};
                
                (* This assumes the receiver is always able to signal that a
                   message was received. *)
                can_send := TRUE;
                
                (* The following snippet would be a way to model the case when
                   receiption acknowledgements get lost. This would result in
                   deadlock: *)
                   
                (*
                either
                    can_send := TRUE;
                or
                    skip;
                end either
                *)
            end with;
        or
            skip;
        end either;
    end while;
    
    assert received = <<1, 2, 3>>;
end algorithm;*)

\* BEGIN TRANSLATION
VARIABLES to_send, received, in_transit, can_send, pc

vars == << to_send, received, in_transit, can_send, pc >>

Init == (* Global variables *)
        /\ to_send = <<1, 2, 3>>
        /\ received = <<>>
        /\ in_transit = {}
        /\ can_send = TRUE
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF Len(received) /= 3
               THEN /\ IF can_send /\ to_send /= <<>>
                          THEN /\ in_transit' = (in_transit \union {Head(to_send)})
                               /\ can_send' = FALSE
                               /\ to_send' = Tail(to_send)
                          ELSE /\ TRUE
                               /\ UNCHANGED << to_send, in_transit, can_send >>
                    /\ \/ /\ pc' = "Lbl_2"
                       \/ /\ TRUE
                          /\ pc' = "Lbl_1"
               ELSE /\ Assert(received = <<1, 2, 3>>, 
                              "Failure of assertion at line 31, column 5.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << to_send, in_transit, can_send >>
         /\ UNCHANGED received

Lbl_2 == /\ pc = "Lbl_2"
         /\ \E msg \in in_transit:
              /\ received' = Append(received, msg)
              /\ in_transit' = in_transit \ {msg}
              /\ can_send' = TRUE
         /\ pc' = "Lbl_1"
         /\ UNCHANGED to_send

Next == Lbl_1 \/ Lbl_2
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Wed Dec 26 11:41:50 GMT 2018 by carlos
\* Created Wed Dec 26 11:17:47 GMT 2018 by carlos
