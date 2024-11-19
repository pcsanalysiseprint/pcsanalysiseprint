dnl Lines starting with 'dnl' are comments for the preprocessor m4.
dnl Tamarin uses '', which is an m4 close quote, so use <! !> for quoting.
changequote(<!,!>)
changecom(<!/*!>, <!*/!>)

theory 

ifelse(BASE, true, <!Base!>,)
ifelse(NR1, true, <!Non_Resilient_Dyn!>,)
ifelse(NR2, true, <!Non_Resilient_Static!>,)
ifelse(R1, true, <!Resilient_Dyn!>,)
ifelse(R2, true, <!Resilient_Static!>,)
ifelse(SEQUENTIAL, true, <!Sequential_Sessions!>,)
ifelse(PROPOSAL, true, <!Proposal!>,)

begin

// Action Fact Legend

// * `CreateDynamicState` records the creation of a new dynamic state (includes attacker states).

// * `HonestCreateDynamicState` records the creation of a new dynamic state (without attacker sessions).

// * `AttackerCreateDynamicStateX` records that the adversary created a new
// dynamic state as party `X`.

// * `Step` records any dynamic state update by honest parties and the attacker.

// * `StepX' records any dynamic state update by honest party X and attacker acting as X.

// * `AttackerStep` records the dynamic state updates by the attacker. 

// * `AttackerStepX` records the dynamic state updates by the attacker acting as X.

// * `HonestStep` records the dynamic state updates by honest parties A or B.

// * `HonestStepX` records the dynamic state updates by honest party X.

// * `RatchetX_Receiver/Sender` records that party `X` acted as
// sender or receiver in a dynamic state update.

// * `AttackerUpdateDynamicStateX_Receiver/Sender` records that the adversary
// updated the dynamic state as party `X` as sender or receiver.

// * `CompromiseB` records that the dynamic state of a party acting as B was compromised.

// * `CompromiseDynamicStateB` additionally records the exact state where the compromised occured.

// * `CompromiseAOrB` records that the dynamic state of a device acting as A or B was compromised.

// * `AttackerKnows` records that the attacker knows a specific secret, e.g.,
// root keys.

// Create a new user
rule CreateUser:
    [ Fr(~id) ]
    -->
    [ !User(~id) ]

// Create a new device
rule CreateUserDevice:
    [ Fr(~did), !User(~uid) ]
    --[ CreatedUserDevice(~uid, ~did) ]->
    [ !UserDevice(~uid, ~did) ]

// Only a single device per user
restriction SingleDevicePerUser:
  "All uid did1 did2 #i #j. CreatedUserDevice(uid, did1) @ i
                          & CreatedUserDevice(uid, did2) @ j
                          ==> #i = #j"


// =============================================================================
// =============================================================================
// ====================== Dynamic State Initialization =========================
// =============================================================================
// =============================================================================

// Create a new dynamic state for two devices with a fresh root key.
// One device will act as user 'A', the other as user 'B'.
rule CreateDynamicState:
    let
        root_keys = <~rk, ~next_rk>
    in
    [ !UserDevice(~uidA, ~idA), !UserDevice(~uidB, ~idB)
    , Fr(~rk), Fr(~next_rk), Fr(~sid) ]
    --[ CreateDynamicState(~sid, ~uidA, ~idA, ~uidB, ~idB, root_keys)
      , HonestCreateDynamicState(~sid, ~uidA, ~idA, ~uidB, ~idB, root_keys) ]->
    [ DynamicStateA(~sid, ~uidA, ~idA, ~uidB, ~idB, root_keys)
    , DynamicStateB(~sid, ~uidA, ~idA, ~uidB, ~idB, root_keys) ]

ifelse(ONE_DYNAMIC, true, <!
// Only a dynamic state between devices
restriction SingleDynamicStateBetweenDevices:
  "All sid1 sid2 uidA idA uidB idB rk1 rk2 #i #j.
   CreateDynamicState(sid1, uidA, idA, uidB, idB, rk1) @ i &
   CreateDynamicState(sid2, uidA, idA, uidB, idB, rk2) @ j ==> #i = #j"
!>,)

// =============================================================================
// =============================================================================
// ========================= Dynamic State Updates =============================
// =============================================================================
// =============================================================================

// User 'A' updates their dynamic state, as if they were sending a message.
// The fact 'UpdateDynamicStateB' is used to trigger a dynamic state update of user 'B'.
rule UpdateDynamicStateA_Sender:
    let
        rks = <old_keys, latest>
        new_rks = <<old_keys, latest>, ~new_rootkey>
    in
    [ DynamicStateA(~sid, ~uidA, ~idA, ~uidB, ~idB, rks)
    , Fr(~new_rootkey) ]
    --[ UpdateDynamicStateA_Sender(~sid, ~uidA, ~idA, ~uidB, ~idB, rks, new_rks)
      , ReceiveOrSend(~sid, ~uidA, ~idA, ~uidB, ~idB, rks, new_rks)
      , Step(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
      , StepA(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
      , HonestStep(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
      , HonestSendStep(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
      , HonestStepA(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks) ]->
    [ DynamicStateA(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
    , !UpdateDynamicStateB(~sid, ~uidA, ~idA, ~uidB, ~idB, rks, new_rks) ]

restriction NoConsecutiveSendingPhasesA:
  "All sid uidA idA uidB idB old_rk new_rk next_rk #i #j.
   UpdateDynamicStateA_Sender(sid, uidA, idA, uidB, idB, old_rk, new_rk) @ i &
   UpdateDynamicStateA_Sender(sid, uidA, idA, uidB, idB, new_rk, next_rk) @ j ==> F"

// User 'B' updates their dynamic state, as if they were receiving a
// message, and updates their dynamic state to the new state.
rule UpdateDynamicStateB_Receiver:
    let
        rks = <old_keys, latest>
        new_rks = <<old_keys, latest>, ~new_rootkey>
    in
    [ DynamicStateB(~sid, ~uidA, ~idA, ~uidB, ~idB, rks)
    , !UpdateDynamicStateB(~sid, ~uidA, ~idA, ~uidB, ~idB, rks, new_rks) ]
    --[ UpdateDynamicStateB_Receiver(~sid, ~uidA, ~idA, ~uidB, ~idB, rks, new_rks)
      , ReceiveOrSend(~sid, ~uidA, ~idA, ~uidB, ~idB, rks, new_rks)
      , Step(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
      , StepB(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
      , HonestStep(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
      , HonestReceiveStep(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
      , HonestStepB(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks) ]->
    [ DynamicStateB(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks) ]

restriction NoConsecutiveReceivingPhasesB:
  "All sid uidA idA uidB idB old_rk new_rk next_rk #i #j.
   UpdateDynamicStateB_Receiver(sid, uidA, idA, uidB, idB, old_rk, new_rk) @ i &
   UpdateDynamicStateB_Receiver(sid, uidA, idA, uidB, idB, new_rk, next_rk) @ j ==> F"

// User 'B' updates their dynamic state, as if they were sending a message.
// The fact 'UpdateDynamicStateA' is used to trigger a dynamic state update of user 'A'.
rule UpdateDynamicStateB_Sender:
    let
        rks = <old_keys, latest>
        new_rks = <<old_keys, latest>, ~new_rootkey>
    in
    [ DynamicStateB(~sid, ~uidA, ~idA, ~uidB, ~idB, rks)
    , Fr(~new_rootkey) ]
    --[ UpdateDynamicStateB_Sender(~sid, ~uidA, ~idA, ~uidB, ~idB, rks, new_rks)
      , ReceiveOrSend(~sid, ~uidA, ~idA, ~uidB, ~idB, rks, new_rks)
      , Step(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
      , StepB(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
      , HonestStep(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
      , HonestSendStep(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
      , HonestStepB(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks) ]->
    [ DynamicStateB(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
    , !UpdateDynamicStateA(~sid, ~uidA, ~idA, ~uidB, ~idB, rks, new_rks) ]

restriction NoConsecutiveSendingPhasesB:
  "All sid uidA idA uidB idB old_rk new_rk next_rk #i #j.
   UpdateDynamicStateB_Sender(sid, uidA, idA, uidB, idB, old_rk, new_rk) @ i &
   UpdateDynamicStateB_Sender(sid, uidA, idA, uidB, idB, new_rk, next_rk) @ j ==> F"

// User 'A' updates their dynamic state, as if they were receiving a
// message, and updates their dynamic state to the new state.
rule UpdateDynamicStateA_Receiver:
    let
        rks = <old_keys, latest>
        new_rks = <<old_keys, latest>, ~new_rootkey>
    in
    [ DynamicStateA(~sid, ~uidA, ~idA, ~uidB, ~idB, rks)
    , !UpdateDynamicStateA(~sid, ~uidA, ~idA, ~uidB, ~idB, rks, new_rks) ]
    --[ UpdateDynamicStateA_Receiver(~sid, ~uidA, ~idA, ~uidB, ~idB, rks, new_rks)
      , ReceiveOrSend(~sid, ~uidA, ~idA, ~uidB, ~idB, rks, new_rks)
      , Step(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
      , StepA(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
      , HonestStep(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
      , HonestReceiveStep(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
      , HonestStepA(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks) ]->
    [ DynamicStateA(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks) ]

restriction NoConsecutiveReceivingPhasesA:
  "All sid uidA idA uidB idB old_rk new_rk next_rk #i #j.
   UpdateDynamicStateA_Receiver(sid, uidA, idA, uidB, idB, old_rk, new_rk) @ i &
   UpdateDynamicStateA_Receiver(sid, uidA, idA, uidB, idB, new_rk, next_rk) @ j ==> F"


// =============================================================================
// =============================================================================
// ======================= Adversary Capabilities ==============================
// =============================================================================
// =============================================================================

// Compromise a device; i.e., static state compromise
rule CompromiseDevice[color=ea3546]:
    [ !UserDevice(~uid, ~did) ]
    --[ CompromiseDevice(~uid, ~did) ]->
    [ !CompromisedDevice(~uid, ~did) ]

restriction SingleCompromiseForSameKeyMaterial:
  "All cid1 cid2 sid uidA idA uidB idB rk #i #j.
   CompromiseDynamicStateAOrB(cid1, sid, uidA, idA, uidB, idB, rk) @ i &
   CompromiseDynamicStateAOrB(cid2, sid, uidA, idA, uidB, idB, rk) @ j ==> #i = #j"

// Create a new dynamic state for a device and an attacker controlled 
// device as 'B'.
rule AttackerCreateDynamicStateB[color=ea3546]:
    let
        root_keys = <~rk, ~next_rk>
    in
    [ !UserDevice(~uidA, ~idA), !CompromisedDevice(~uidB, ~idB)
    , Fr(~rk), Fr(~next_rk), Fr(~sid), Fr(~cid) ]
    --[ CreateDynamicState(~sid, ~uidA, ~idA, ~uidB, ~idB, root_keys)
      , AttackerCreateDynamicStateB(~cid, ~sid, ~uidA, ~idA, ~uidB, ~idB, root_keys) ]->
    [ DynamicStateA(~sid, ~uidA, ~idA, ~uidB, ~idB, root_keys)
    , CompromisedDynamicStateB(~cid, ~sid, ~uidA, ~idA, ~uidB, ~idB, root_keys) ]

// Create a new dynamic state for a device and an attacker controlled 
// device as 'A'.
rule AttackerCreateDynamicStateA[color=ea3546]:
    let
        root_keys = <~rk, ~next_rk>
    in
    [ !CompromisedDevice(~uidA, ~idA), !UserDevice(~uidB, ~idB)
    , Fr(~rk), Fr(~next_rk), Fr(~sid), Fr(~cid) ]
    --[ CreateDynamicState(~sid, ~uidA, ~idA, ~uidB, ~idB, root_keys)
      , AttackerCreateDynamicStateA(~cid, ~sid, ~uidA, ~idA, ~uidB, ~idB, root_keys) ]->
    [ DynamicStateB(~sid, ~uidA, ~idA, ~uidB, ~idB, root_keys)
    , CompromisedDynamicStateA(~cid, ~sid, ~uidA, ~idA, ~uidB, ~idB, root_keys) ]

// The adversary compromises the dynamic state of 'A'. The fresh 'cid' is just
// an identifier for the compromised state to be injective.
rule CompromiseDynamicStateA[color=ea3546]:
    let
        rks = <old_keys, latest>
    in
    [ DynamicStateA(~sid, ~uidA, ~idA, ~uidB, ~idB, rks), Fr(~cid) ]
    --[ CompromiseA(~uidA, ~idA, ~uidB, ~idB, rks)
      , CompromiseDynamicStateA(~cid, ~sid, ~uidA, ~idA, ~uidB, ~idB, rks)
      , CompromiseAOrB(~uidA, ~idA, ~uidB, ~idB, rks)
      , CompromiseDynamicStateAOrB(~cid, ~sid, ~uidA, ~idA, ~uidB, ~idB, rks)
      , Step(~sid, ~uidA, ~idA, ~uidB, ~idB, rks)
      , StepA(~sid, ~uidA, ~idA, ~uidB, ~idB, rks)
      , HonestStepA(~sid, ~uidA, ~idA, ~uidB, ~idB, rks)
      , AttackerKnows(rks) ]->
    [ CompromisedDynamicStateA(~cid, ~sid, ~uidA, ~idA, ~uidB, ~idB, rks)
    , DynamicStateA(~sid, ~uidA, ~idA, ~uidB, ~idB, rks) ]


// The adversary compromises the dynamic state of 'B'. The fresh 'cid' is just an
// identifier for the compromised state to be injective.
rule CompromiseDynamicStateB[color=ea3546]:
    let
        rks = <old_keys, latest>
    in
    [ DynamicStateB(~sid, ~uidA, ~idA, ~uidB, ~idB, rks), Fr(~cid) ]
    --[ CompromiseB(~uidA, ~idA, ~uidB, ~idB, rks)
      , CompromiseDynamicStateB(~cid, ~sid, ~uidA, ~idA, ~uidB, ~idB, rks)
      , CompromiseAOrB(~uidA, ~idA, ~uidB, ~idB, rks)
      , CompromiseDynamicStateAOrB(~cid, ~sid, ~uidA, ~idA, ~uidB, ~idB, rks)
      , Step(~sid, ~uidA, ~idA, ~uidB, ~idB, rks)
      , StepB(~sid, ~uidA, ~idA, ~uidB, ~idB, rks)
      , HonestStepB(~sid, ~uidA, ~idA, ~uidB, ~idB, rks)
      , AttackerKnows(rks) ]->
    [ CompromisedDynamicStateB(~cid, ~sid, ~uidA, ~idA, ~uidB, ~idB, rks)
    ,  DynamicStateB(~sid, ~uidA, ~idA, ~uidB, ~idB, rks) ]

// Compromised 'A' updates their dynamic state, as if they were sending a message.
// The fact 'UpdateDynamicStateB' is used to trigger a dynamic state update of user 'B'.
rule AttackerUpdateDynamicStateA_Sender[color=ea3546]:
    let
        rks = <old_keys, latest>
        new_rks = <<old_keys, latest>, ~new_rootkey>
    in
    [ CompromisedDynamicStateA(~cid, ~sid, ~uidA, ~idA, ~uidB, ~idB, rks)
    , Fr(~new_rootkey) ]
    --[ AttackerUpdateDynamicStateA_Sender(~sid, ~uidA, ~idA, ~uidB, ~idB, rks, new_rks)
      , Step(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
      , StepA(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
      , AttackerStep(~cid, ~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
      , AttackerStepA(~cid, ~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
      , AttackerKnows(new_rks) ]->
    [ CompromisedDynamicStateA(~cid, ~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
    , !UpdateDynamicStateB(~sid, ~uidA, ~idA, ~uidB, ~idB, rks, new_rks) ]

// Compromised 'B' updates their dynamic state, as if they were receiving a
// message, and updates their dynamic state to the new state.
rule AttackerUpdateDynamicStateB_Receiver[color=ea3546]:
    let
        rks = <old_keys, latest>
        new_rks = <<old_keys, latest>, ~new_rootkey>
    in
    [ CompromisedDynamicStateB(~cid, ~sid, ~uidA, ~idA, ~uidB, ~idB, rks)
    , !UpdateDynamicStateB(~sid, ~uidA, ~idA, ~uidB, ~idB, rks, new_rks) ]
    --[ AttackerUpdateDynamicStateB_Receiver(~sid, ~uidA, ~idA, ~uidB, ~idB, rks, new_rks)
      , Step(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
      , StepB(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
      , AttackerStep(~cid, ~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
      , AttackerStepB(~cid, ~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
      , AttackerKnows(new_rks) ]->
    [ CompromisedDynamicStateB(~cid, ~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks) ]

// Compromised 'B' updates their dynamic state, as if they were sending a message.
// The fact 'UpdateDynamicStateA' is used to trigger a dynamic state update of user 'A'.
rule AttackerUpdateDynamicStateB_Sender[color=ea3546]:
    let
        rks = <old_keys, latest>
        new_rks = <<old_keys, latest>, ~new_rootkey>
    in
    [ CompromisedDynamicStateB(~cid, ~sid, ~uidA, ~idA, ~uidB, ~idB, rks)
    , Fr(~new_rootkey) ]
    --[ AttackerUpdateDynamicStateB_Sender(~sid, ~uidA, ~idA, ~uidB, ~idB, rks, new_rks)
      , Step(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
      , StepB(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
      , AttackerStep(~cid, ~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
      , AttackerStepB(~cid, ~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
      , AttackerKnows(new_rks) ]->
    [ CompromisedDynamicStateB(~cid, ~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
    , !UpdateDynamicStateA(~sid, ~uidA, ~idA, ~uidB, ~idB, rks, new_rks) ]

// Compromised 'A' updates their dynamic state, as if they were receiving a
// message, and updates their dynamic state to the new state.
rule AttackerUpdateDynamicStateA_Receiver[color=ea3546]:
    let
        rks = <old_keys, latest>
        new_rks = <<old_keys, latest>, ~new_rootkey>
    in
    [ CompromisedDynamicStateA(~cid, ~sid, ~uidA, ~idA, ~uidB, ~idB, rks)
    , !UpdateDynamicStateA(~sid, ~uidA, ~idA, ~uidB, ~idB, rks, new_rks) ]
    --[ AttackerUpdateDynamicStateA_Receiver(~sid, ~uidA, ~idA, ~uidB, ~idB, rks, new_rks)
      , Step(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
      , StepA(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
      , AttackerStep(~cid, ~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
      , AttackerStepA(~cid, ~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
      , AttackerKnows(new_rks) ]->
    [ CompromisedDynamicStateA(~cid, ~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks) ]

// =============================================================================
// =============================================================================
// ============================== State Loss ===================================
// =============================================================================
// =============================================================================

ifelse(DYNAMIC_STATE_LOSS, true, <!
// 'A' loses a dynamic state.
rule DynamicStateLossA:
    let
        rks = <old_keys, latest>
    in
    [ DynamicStateA(~sid, ~uidA, ~idA, ~uidB, ~idB, rks) ]
    --[ DynamicStateLossA(~sid, ~uidA, ~idA, ~uidB, ~idB, rks) ]->
    []

// 'B' loses dynamic state.
rule DynamicStateLossB:
    let
        rks = <old_keys, latest>
    in
    [ DynamicStateB(~sid, ~uidA, ~idA, ~uidB, ~idB, rks) ]
    --[ DynamicStateLossB(~sid, ~uidA, ~idA, ~uidB, ~idB, rks) ]-> 
    [] 
!>,)

ifelse(STATIC_STATE_LOSS, true, <!
rule StaticStateLoss:
  [ !UserDevice(~uid, ~did) ]
  --[ StaticStateLoss(~uid, ~did) ]->
  []

restriction StaticStateLossTerminatesDynamicStateA:
  "All sid uidA idA uidB idB rks #i #j.
   StaticStateLoss(uidA, idA) @ i &
   HonestStep(sid, uidA, idA, uidB, idB, rks) @ j &
   #i < #j ==> (Ex #h. StaticStateRecovery(uidA, idA) @ h & #i < #h & #h < #j)"

restriction StaticStateLossTerminatesDynamicStateB:
  "All sid uidA idA uidB idB rks #i #j.
   StaticStateLoss(uidB, idB) @ i &
   HonestStep(sid, uidA, idA, uidB, idB, rks) @ j &
   #i < #j ==> (Ex #h. StaticStateRecovery(uidB, idB) @ h & #i < #h & #h < #j)"
!>,)


ifelse(STATIC_STATE_RECOVERY, true, <!
rule StaticStateRecovery:
  [ !UserDevice(~uid, ~did) ]
  --[ StaticStateRecovery(~uid, ~did) ]->
  []
!>,)

// =============================================================================
// =============================================================================
// =========================== Session Policies ================================
// =============================================================================
// =============================================================================

ifelse(SEQUENTIAL_SESSIONS, true, <!
// User 'B' updates their dynamic state, as if they were receiving a
// message, and updates their dynamic state to the new state.
// This rule handles the out-of-order receive from an older dynamic state
// of the peer.
rule UpdateDynamicStateB_Receiver_OOO:
    let
        rks = <old_keys, latest>
        new_rks = <<old_keys, latest>, ~new_rootkey>
    in
    [ DynamicStateB(~sid, ~uidA, ~idA, ~uidB, ~idB, rks)
    , !UpdateDynamicStateB(~sid, ~uidA, ~idA, ~uidB, ~idB, rks, new_rks) ]
    --[ UpdateDynamicStateB_Receiver_OOO(~sid, ~uidA, ~idA, ~uidB, ~idB, rks, new_rks)
      , Step(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
      , StepB(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
      , HonestStep(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
      , HonestStepB(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks) ]->
    [ DynamicStateB(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks) ]

// User 'A' updates their dynamic state, as if they were receiving a
// message, and updates their dynamic state to the new state.
// This rule handles the out-of-order receive from an older dynamic state
// of the peer.
rule UpdateDynamicStateA_Receiver_OOO:
    let
        rks = <old_keys, latest>
        new_rks = <<old_keys, latest>, ~new_rootkey>
    in
    [ DynamicStateA(~sid, ~uidA, ~idA, ~uidB, ~idB, rks)
    , !UpdateDynamicStateA(~sid, ~uidA, ~idA, ~uidB, ~idB, rks, new_rks) ]
    --[ UpdateDynamicStateA_Receiver_OOO(~sid, ~uidA, ~idA, ~uidB, ~idB, rks, new_rks)
      , Step(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
      , StepA(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
      , HonestStep(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
      , HonestStepA(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks)
    ]->
    [ DynamicStateA(~sid, ~uidA, ~idA, ~uidB, ~idB, new_rks) ]

// Sending is only allowed from the currently active session.
restriction SequentialSessions_Sending:
  "All sid1 sid2 uidA idA uidB idB rk1 rk2 rk3 #i #j #k.
   CreateDynamicState(sid1, uidA, idA, uidB, idB, rk1) @ i &
   CreateDynamicState(sid2, uidA, idA, uidB, idB, rk2) @ j & i<j &
   HonestSendStep(sid1, uidA, idA, uidB, idB, rk3) @ k & j<k
   ==> F"

// Receiving 'real' message is only allowed in the active session.
// Out-of-order messages can be received in all sessions.
restriction SequentialSessions_Receiving:
  "All sid1 sid2 uidA idA uidB idB rk1 rk2 rk3 #i #j #k.
   CreateDynamicState(sid1, uidA, idA, uidB, idB, rk1) @ i &
   CreateDynamicState(sid2, uidA, idA, uidB, idB, rk2) @ j & i<j &
   HonestReceiveStep(sid1, uidA, idA, uidB, idB, rk3) @ k & j<k
   ==> F"

restriction NoConsecutiveReceivingPhasesB1:
  "All sid uidA idA uidB idB old_rk new_rk next_rk #i #j.
   UpdateDynamicStateB_Receiver(sid, uidA, idA, uidB, idB, old_rk, new_rk) @ i &
   UpdateDynamicStateB_Receiver_OOO(sid, uidA, idA, uidB, idB, new_rk, next_rk) @ j ==> F"

restriction NoConsecutiveReceivingPhasesB2:
  "All sid uidA idA uidB idB old_rk new_rk next_rk #i #j.
   UpdateDynamicStateB_Receiver_OOO(sid, uidA, idA, uidB, idB, old_rk, new_rk) @ i &
   UpdateDynamicStateB_Receiver(sid, uidA, idA, uidB, idB, new_rk, next_rk) @ j ==> F"

restriction NoConsecutiveReceivingPhasesB3:
  "All sid uidA idA uidB idB old_rk new_rk next_rk #i #j.
   UpdateDynamicStateB_Receiver_OOO(sid, uidA, idA, uidB, idB, old_rk, new_rk) @ i &
   UpdateDynamicStateB_Receiver_OOO(sid, uidA, idA, uidB, idB, new_rk, next_rk) @ j ==> F"

restriction NoConsecutiveReceivingPhasesA1:
  "All sid uidA idA uidB idB old_rk new_rk next_rk #i #j.
   UpdateDynamicStateA_Receiver(sid, uidA, idA, uidB, idB, old_rk, new_rk) @ i &
   UpdateDynamicStateA_Receiver_OOO(sid, uidA, idA, uidB, idB, new_rk, next_rk) @ j ==> F"

restriction NoConsecutiveReceivingPhasesA2:
  "All sid uidA idA uidB idB old_rk new_rk next_rk #i #j.
   UpdateDynamicStateA_Receiver_OOO(sid, uidA, idA, uidB, idB, old_rk, new_rk) @ i &
   UpdateDynamicStateA_Receiver(sid, uidA, idA, uidB, idB, new_rk, next_rk) @ j ==> F"

restriction NoConsecutiveReceivingPhasesA3:
  "All sid uidA idA uidB idB old_rk new_rk next_rk #i #j.
   UpdateDynamicStateA_Receiver_OOO(sid, uidA, idA, uidB, idB, old_rk, new_rk) @ i &
   UpdateDynamicStateA_Receiver_OOO(sid, uidA, idA, uidB, idB, new_rk, next_rk) @ j ==> F"


!>,)

ifelse(PROPOSAL, true, <!
// Only out-of-order receives from N<=2 latest sessions.
restriction OutOfOrderA:
  "All sid1 sid2 sid3 uidA idA uidB idB rk1 rk2 rk3 rk4 rk5 #i #j #k #l.
   CreateDynamicState(sid1, uidA, idA, uidB, idB, rk1) @ i &
   CreateDynamicState(sid2, uidA, idA, uidB, idB, rk2) @ j & i<j &
   CreateDynamicState(sid3, uidA, idA, uidB, idB, rk3) @ k & j<k &
   UpdateDynamicStateA_Receiver_OOO(sid1, uidA, idA, uidB, idB, rk4, rk5) @ l & k<l
   ==> F"

// Only out-of-order receives from N<=2 latest sessions.
restriction OutOfOrderB:
  "All sid1 sid2 sid3 uidA idA uidB idB rk1 rk2 rk3 rk4 rk5 #i #j #k #l.
   CreateDynamicState(sid1, uidA, idA, uidB, idB, rk1) @ i &
   CreateDynamicState(sid2, uidA, idA, uidB, idB, rk2) @ j & i<j &
   CreateDynamicState(sid3, uidA, idA, uidB, idB, rk3) @ k & j<k &
   UpdateDynamicStateB_Receiver_OOO(sid1, uidA, idA, uidB, idB, rk4, rk5) @ l & k<l
   ==> F"
!>,)

// =============================================================================
// =============================================================================
// ============================ Sanity Lemmas ==================================
// =============================================================================
// =============================================================================

ifelse(SEQUENTIAL_SESSIONS, true, <!
// Out-of-order receive can be triggered for A.
lemma SANITY_OOO_ReceiveA: exists-trace
    "Ex sid uidA idA uidB idB rk new_rk #i.
     UpdateDynamicStateA_Receiver_OOO(sid, uidA, idA, uidB, idB, rk, new_rk) @ i"

// Out-of-order receive can be triggered for B.
lemma SANITY_OOO_ReceiveB: exists-trace
    "Ex sid uidA idA uidB idB rk new_rk #i.
     UpdateDynamicStateB_Receiver_OOO(sid, uidA, idA, uidB, idB, rk, new_rk) @ i"
!>,)

// 'A' updates first and 'B' follows.
lemma SANITY_RatchetASender: exists-trace
    "Ex sid uidA idA uidB idB rk new_rk #i #j.
     UpdateDynamicStateA_Sender(sid, uidA, idA, uidB, idB, rk, new_rk) @ i &
     UpdateDynamicStateB_Receiver(sid, uidA, idA, uidB, idB, rk, new_rk) @ j"

// 'B' updates first and 'A' follows.
lemma SANITY_RatchetBSender: exists-trace
    "Ex sid uidA idA uidB idB rk new_rk #i #j.
     UpdateDynamicStateB_Sender(sid, uidA, idA, uidB, idB, rk, new_rk) @ i &
     UpdateDynamicStateA_Receiver(sid, uidA, idA, uidB, idB, rk, new_rk) @ j"

// 'B' updates first and 'A' follows, and then the other way around.
lemma SANITY_RatchetContinued: exists-trace
    "Ex sid uidA idA uidB idB rk new_rk next_rk #i #j #k #l.
     UpdateDynamicStateB_Sender(sid, uidA, idA, uidB, idB, rk, new_rk) @ i & #i < #j &
     UpdateDynamicStateA_Receiver(sid, uidA, idA, uidB, idB, rk, new_rk) @ j & #j < #k &
     UpdateDynamicStateA_Sender(sid, uidA, idA, uidB, idB, new_rk, next_rk) @ k & #k < #l &
     UpdateDynamicStateB_Receiver(sid, uidA, idA, uidB, idB, new_rk, next_rk) @ l"

// Compromised 'A' updates and 'B' follows.
lemma SANITY_RatchetCompromisedASender: exists-trace
    "Ex sid uidA idA uidB idB rk new_rk #i #j.
     AttackerUpdateDynamicStateA_Sender(sid, uidA, idA, uidB, idB, rk, new_rk) @ i &
     UpdateDynamicStateB_Receiver(sid, uidA, idA, uidB, idB, rk, new_rk) @ j"

// Compromised 'B' updates and 'A' follows.
lemma SANITY_RatchetCompromisedBSender: exists-trace
    "Ex sid uidA idA uidB idB rk new_rk #i #j.
     AttackerUpdateDynamicStateB_Sender(sid, uidA, idA, uidB, idB, rk, new_rk) @ i &
     UpdateDynamicStateA_Receiver(sid, uidA, idA, uidB, idB, rk, new_rk) @ j"

// 'B' updates first and compromised 'A' follows, and then the other way around.
lemma SANITY_RatchetCompromisedContinued: exists-trace
    "Ex sid uidA idA uidB idB rk new_rk next_rk #i #j #k #l.
     UpdateDynamicStateB_Sender(sid, uidA, idA, uidB, idB, rk, new_rk) @ i &
     AttackerUpdateDynamicStateA_Receiver(sid, uidA, idA, uidB, idB, rk, new_rk) @ j &
     AttackerUpdateDynamicStateA_Sender(sid, uidA, idA, uidB, idB, new_rk, next_rk) @ k &
     UpdateDynamicStateB_Receiver(sid, uidA, idA, uidB, idB, new_rk, next_rk) @ l"

// Attacker creates a state as 'A', 'B' updates first and compromised 'A'
// follows, and then the other way around.
lemma SANITY_AttackerCreateDynamicStateRatchetCompromisedContinued: exists-trace
    "Ex cid sid uidA idA uidB idB rk new_rk next_rk #h #i #j #k #l.
     AttackerCreateDynamicStateA(cid, sid, uidA, idA, uidB, idB, rk) @ h &
     UpdateDynamicStateB_Sender(sid, uidA, idA, uidB, idB, rk, new_rk) @ i &
     AttackerUpdateDynamicStateA_Receiver(sid, uidA, idA, uidB, idB, rk, new_rk) @ j &
     AttackerUpdateDynamicStateA_Sender(sid, uidA, idA, uidB, idB, new_rk, next_rk) @ k &
     UpdateDynamicStateB_Receiver(sid, uidA, idA, uidB, idB, new_rk, next_rk) @ l"
    
ifelse(DYNAMIC_STATE_LOSS, true, <!
lemma SANITY_DynamicStateLossAPossible: exists-trace
    "Ex sid uidA idA uidB idB rk new_rk next_rk #i #j #k #l #m.
     UpdateDynamicStateB_Sender(sid, uidA, idA, uidB, idB, rk, new_rk) @ i &
     UpdateDynamicStateA_Receiver(sid, uidA, idA, uidB, idB, rk, new_rk) @ j &
     UpdateDynamicStateA_Sender(sid, uidA, idA, uidB, idB, new_rk, next_rk) @ k &
     UpdateDynamicStateB_Receiver(sid, uidA, idA, uidB, idB, new_rk, next_rk) @ l &
     DynamicStateLossA(sid, uidA, idA, uidB, idB, next_rk) @ m"

lemma SANITY_DynamicStateLossBPossible[heuristic=C]: exists-trace
    "Ex sid uidA idA uidB idB rk new_rk next_rk #i #j #k #l #m.
     UpdateDynamicStateB_Sender(sid, uidA, idA, uidB, idB, rk, new_rk) @ i &
     UpdateDynamicStateA_Receiver(sid, uidA, idA, uidB, idB, rk, new_rk) @ j &
     UpdateDynamicStateA_Sender(sid, uidA, idA, uidB, idB, new_rk, next_rk) @ k &
     UpdateDynamicStateB_Receiver(sid, uidA, idA, uidB, idB, new_rk, next_rk) @ l &
     DynamicStateLossB(sid, uidA, idA, uidB, idB, next_rk) @ m"
!>,)

// =============================================================================
// =============================================================================
// =============================== Tactics =====================================
// =============================================================================
// =============================================================================

tactic: StateA
prio:
  regex "HonestStepA\(" | regex "HonestStep"
prio:
  regex "CreateDynamicState\("
prio:
  regex "DynamicStateA\("

tactic: StateB
prio:
  regex "HonestStepB\(" | regex "HonestStep"
prio:
  regex "CreateDynamicState\("
prio:
  regex "DynamicStateB\("

tactic: State
prio:
  regex "HonestStepA\(" | regex "HonestStepB\(" | regex "HonestStep\("
prio:
  regex "CreateDynamicState\("
prio:
  regex "DynamicStateA\(" | regex "DynamicStateB\("

tactic: CompromisedStateA
prio:
  regex "AttackerStepA\(" | regex "AttackerStep"
prio:
  regex "CreateDynamicState\("
prio:
  regex "DynamicStateA\(" | regex "DynamicStateB"



// =============================================================================
// =============================================================================
// =========================== Helper Lemmas ===================================
// =============================================================================
// =============================================================================

tactic: StepCreateDynamicStateOrdered
prio:
  regex "Step\("
prio:
  regex "CreateDynamicState\("

// Dynamic state must always be created before any step
lemma AUTOMATIC_StepCreateDynamicStateOrdered[use_induction, heuristic={StepCreateDynamicStateOrdered}, reuse]:
    "All sid uidA1 uidA2 idA1 idA2 uidB1 uidB2 idB1 idB2 rk1 rk2 #i #j.
    CreateDynamicState(sid, uidA1, idA1, uidB1, idB1, rk1)@#i &
    Step(sid, uidA2, idA2, uidB2, idB2, rk2)@#j
    ==> (#i < #j & uidA1 = uidA2 & idA1 = idA2 & uidB1 = uidB2
    & idB1 = idB2)"

lemma AUTOMATIC_CreateDynamicStateUniqueForSid[use_induction, reuse]:
    "All sid uidA1 uidA2 idA1 idA2 uidB1 uidB2 idB1 idB2 rk1 rk2 #i #j.
    CreateDynamicState(sid, uidA1, idA1, uidB1, idB1, rk1)@#i &
    CreateDynamicState(sid, uidA2, idA2, uidB2, idB2, rk2)@#j
    ==> #i = #j"

lemma AUTOMATIC_HonestStepAExcludesAttackerStartedA[use_induction, reuse]:
    "All sid cid uidA1 uidA2 idA1 idA2 uidB1 uidB2 idB1 idB2 rk1 rk2 #i #j.
    HonestStepA(sid, uidA1, idA1, uidB1, idB1, rk1)@#i &
    AttackerCreateDynamicStateA(cid, sid, uidA2, idA2, uidB2, idB2, rk2)@#j
    ==> F"

lemma AUTOMATIC_HonestStepBExcludesAttackerStartedB[use_induction, reuse]:
    "All sid cid uidA1 uidA2 idA1 idA2 uidB1 uidB2 idB1 idB2 rk1 rk2 #i #j.
    HonestStepB(sid, uidA1, idA1, uidB1, idB1, rk1)@#i &
    AttackerCreateDynamicStateB(cid, sid, uidA2, idA2, uidB2, idB2, rk2)@#j
    ==> F"

lemma AUTOMATIC_HonestStepAWellfounded[use_induction, reuse]:
    "All sid uidA idA uidB idB rk #i.
    HonestStepA(sid, uidA, idA, uidB, idB, rk)@#i 
    ==> Ex rk2 #j. j<i & CreateDynamicState(sid, uidA, idA, uidB, idB, rk2)@#j"

lemma AUTOMATIC_HonestStepBWellfounded[use_induction, reuse]:
    "All sid uidA idA uidB idB rk #i.
    HonestStepB(sid, uidA, idA, uidB, idB, rk)@#i 
    ==> Ex rk2 #j. j<i & CreateDynamicState(sid, uidA, idA, uidB, idB, rk2)@#j"

lemma AUTOMATIC_AttackerStepAWellfounded[use_induction, reuse]:
    "(All sid cid uidA idA uidB idB rk1 #i.
    AttackerStepA(cid, sid, uidA, idA, uidB, idB, rk1)@#i
    ==> (Ex rk2 #j. CompromiseDynamicStateA(cid, sid, uidA, idA, uidB, idB, rk2)@#j
         & #j < #i)
    | (Ex rk2 #j. AttackerCreateDynamicStateA(cid, sid, uidA, idA, uidB, idB, rk2)@#j
       & #j <#i))"

lemma AUTOMATIC_AttackerStepBWellfounded[use_induction, heuristic=i, reuse]:
    "(All sid cid uidA idA uidB idB rk1 #i.
    AttackerStepB(cid, sid, uidA, idA, uidB, idB, rk1)@#i
    ==> (Ex rk2 #j. CompromiseDynamicStateB(cid, sid, uidA, idA, uidB, idB, rk2)@#j
         & #j < #i)
    | (Ex rk2 #j. AttackerCreateDynamicStateB(cid, sid, uidA, idA, uidB, idB, rk2)@#j
       & #j <#i))"

lemma AUTOMATIC_StepATotallyOrdered[heuristic=C, reuse]:
    "All sid uidA1 uidA2 idA1 idA2 uidB1 uidB2 idB1 idB2 rk1 rk2 #i #j.
    StepA(sid, uidA1, idA1, uidB1, idB1, rk1)@#i &
    StepA(sid, uidA2, idA2, uidB2, idB2, rk2)@#j & not(rk1 = rk2)
    ==> #i < #j | #j < #i"

lemma AUTOMATIC_StepBTotallyOrdered[heuristic=C, reuse]:
    "All sid uidA1 uidA2 idA1 idA2 uidB1 uidB2 idB1 idB2 rk1 rk2 #i #j.
    StepB(sid, uidA1, idA1, uidB1, idB1, rk1)@#i &
    StepB(sid, uidA2, idA2, uidB2, idB2, rk2)@#j & not(rk1 = rk2)
    ==> #i < #j | #j < #i"


ifelse(DYNAMIC_STATE_LOSS, true, <!
lemma AUTOMATIC_HonestStepABeforeDynamicStateLossA[use_induction, heuristic={State}, reuse]:
    "(All sid uidA idA uidB idB rk1 rk2 #i #j.
    HonestStepA(sid, uidA, idA, uidB, idB, rk1)@#i &
    DynamicStateLossA(sid, uidA, idA, uidB, idB, rk2)@#j
    ==> (#i < #j))"

lemma AUTOMATIC_HonestStepBBeforeDynamicStateLossB[use_induction, heuristic={State}, reuse]:
    "(All sid uidA idA uidB idB rk1 rk2 #i #j.
    HonestStepB(sid, uidA, idA, uidB, idB, rk1)@#i &
    DynamicStateLossB(sid, uidA, idA, uidB, idB, rk2)@#j
    ==> (#i < #j))"
!>,)

tactic: HonestStep
prio:
  regex "HonestStepA\(" | regex "HonestStepB\(" | regex "HonestStep\("
prio:
  regex "!UpdateDynamicStateA\(" | regex "!UpdateDynamicStateB\("

// No longer automatically proves now that compromising the session state loops.
lemma AUTOMATIC_HonestStepWithSameRKImpliesSameSid[heuristic={HonestStep}, reuse]:
    "All sid1 sid2 uidA1 uidA2 idA1 idA2 uidB1 uidB2 idB1 idB2 rk #i #j.
    HonestStep(sid1, uidA1, idA1, uidB1, idB1, rk)@#i &
    HonestStep(sid2, uidA2, idA2, uidB2, idB2, rk)@#j
    ==> sid1 = sid2"

tactic: AttackerStep
prio:
  regex "AttackerStepA\(" | regex "AttackerStepB\(" | regex "AttackerStep\("
prio:
  regex "!UpdateDynamicStateA\(" | regex "!UpdateDynamicStateB\("

lemma AUTOMATIC_AttackerStepWithSameRKImpliesSameSid[heuristic={AttackerStep}, reuse]:
    "All cid1 cid2 sid1 sid2 uidA1 uidA2 idA1 idA2 uidB1 uidB2 idB1 idB2 rk #i #j.
    AttackerStep(cid1, sid1, uidA1, idA1, uidB1, idB1, rk)@#i &
    AttackerStep(cid2, sid2, uidA2, idA2, uidB2, idB2, rk)@#j
    ==> sid1 = sid2"

// =============================================================================
// =============================================================================
// ============================= Statements ====================================
// =============================================================================
// =============================================================================

tactic: PCS
prio:
  regex "!CompromisedDevice\("
prio:
  regex "ReceiveOrSend\(" | regex "AttackerKnows\("

define(<!NEGDEF1!>, <!
// A stronger version of the negation of Definition 1.
// We prove that after every dynamic state loss there are no more honest
// state updates of that state, i.e., a benign user is unable to use the state
// after the loss. This is stronger than the negation of Definition 1, which
// simply states that there exists a state which cannot progress.
lemma AUTOMATIC_DynamicStateLossImpliesNoSteps[heuristic={State}]:
    "All sid1 uidA idA uidB idB rk1 #i.
    DynamicStateLossA(sid1, uidA, idA, uidB, idB, rk1)@#i 
    ==> not(Ex #j sid2 rk2. i<j & HonestStepA(sid2, uidA, idA, uidB, idB, rk2)@#j)
    "
!>)

define(<!DEF1!>, <!
// A weaker version Definition 1.
// Instead of showing that after every dynamic state loss, there exists the
// option to continue with the communication, we show that there exists a
// trace where after some dynamic state loss the communication continues.
lemma AUTOMATIC_StepAfterDynamicStateLoss[heuristic={State}]: exists-trace
    "Ex sid1 sid2 uidA idA uidB idB rk1 rk2 #i #j.
    DynamicStateLossA(sid1, uidA, idA, uidB, idB, rk1)@#i & i<j &
    HonestStepA(sid2, uidA, idA, uidB, idB, rk2)@#j
    "
!>)

define(<!NEGDEF2!>, <!
// A stronger version of the negation of Definition 2.
// We prove that after every static state loss there are no more honest
// state updates of that state, i.e., a benign user is unable to use the state
// after the loss. This is stronger than the negation of Definition 2, which
// simply states that there exists a state which cannot progress.
lemma AUTOMATIC_StaticStateLossImpliesNoSteps[heuristic=C]:
    "All uid did #i .
     StaticStateLoss(uid, did)@#i 
    ==> not(Ex #j sid uidB idB rk. i<j & HonestStep(sid, uid, did, uidB, idB, rk)@#j)
    "
!>)

define(<!DEF2!>, <!
// A weaker version Definition 2.
// Instead of showing that after every static state loss, there exists the
// option to continue with the communication, we show that there exists a
// trace where after some static state loss the communication continues.
lemma AUTOMATIC_StepAfterStaticStateLoss[heuristic={State}]: exists-trace
    "Ex sid uid did uidB idB rk #i #j.
     StaticStateLoss(uid, did)@#i & #i<#j &
     HonestStep(sid, uid, did, uidB, idB, rk)@#j
    "
!>)

define(<!DEF4!>, <!
// Definition 4. Session PCS - Full Compromise
// TODO: This restriction somehow influences the induction hypotheses of previous
// lemmas, which causes them to no longer terminate. To avoid this, we turned
// the restriction into a lemma but do not prove it. As a result, it is only
// in scope for lemmas below this lemma and does not influence lemmas before it.
lemma NOPROVE_SessionPCS_FullCompromise[reuse]:
    " All uidA idA uidB idB rk1 rk2 rk3 rk4 rk5 rk6 sid1 #i2 #i3 #i4 #i5.
      #i2<#i3
    & #i3 <#i4
    & UpdateDynamicStateA_Sender(sid1, uidA, idA, uidB, idB, rk1, rk2)@#i2
    & UpdateDynamicStateA_Receiver(sid1, uidA, idA, uidB, idB, rk3, rk4)@#i3
    & ReceiveOrSend(sid1, uidA, idA, uidB, idB, rk5, rk6)@#i4
    & AttackerKnows(rk5)@#i5

    ==> 
        // PCS, Attacker compromised again
        (Ex rk7 #l. #i2<#l & CompromiseA(uidA, idA, uidB, idB, rk7)@l)
        // The partner was compromised and A is talking to the attacker.
    |   (Ex rk7 #l. CompromiseB(uidA, idA, uidB, idB, rk7)@l)
        // Attacker compromises the device and started a session themselves
    |   (Ex #l. #i2 < #l & CompromiseDevice(uidA, idA)@l)
    |   (Ex #l. CompromiseDevice(uidB, idB)@l)
    "
!>)

define(<!DEF5!>, <!

// Definition 5. Conversation PCS - Session Compromise
lemma ConversationPCS_SessionCompromise[heuristic={PCS}]:
    " All uidA idA uidB idB rk1 rk2 rk3 rk4 rk5 rk6 sid1 sid2 sid3 #i2 #i3 #i4 #i5.
      #i2<#i3
    & #i3 <#i4
    & UpdateDynamicStateA_Sender(sid1, uidA, idA, uidB, idB, rk1, rk2)@#i2
    & UpdateDynamicStateA_Receiver(sid2, uidA, idA, uidB, idB, rk3, rk4)@#i3
    & ReceiveOrSend(sid3, uidA, idA, uidB, idB, rk5, rk6)@#i4
    & AttackerKnows(rk5)@#i5

    ==> 
        // PCS, Attacker compromised again
        (Ex rk7 #l. #i2<#l & CompromiseA(uidA, idA, uidB, idB, rk7)@l)
        // The partner was compromised and A is talking to the attacker.
    |   (Ex rk7 #l. CompromiseB(uidA, idA, uidB, idB, rk7)@l)
        // Attacker compromises the device and started a session themselves
    |   (Ex #l. CompromiseDevice(uidA, idA)@l)
    |   (Ex #l. CompromiseDevice(uidB, idB)@l)
    "

!>)

define(<!DEF6!>, <!

// Definition 6. Conversation PCS - Full Compromise
// We never prove this property, but use it for attack finding
lemma ConversationPCS_FullCompromise[heuristic={PCS}]:
    " All uidA idA uidB idB rk1 rk2 rk3 rk4 rk5 rk6 sid1 sid2 sid3 #i2 #i3 #i4 #i5.
      #i2<#i3
    & #i3 <#i4
    & UpdateDynamicStateA_Sender(sid1, uidA, idA, uidB, idB, rk1, rk2)@#i2
    & UpdateDynamicStateA_Receiver(sid2, uidA, idA, uidB, idB, rk3, rk4)@#i3
    & ReceiveOrSend(sid3, uidA, idA, uidB, idB, rk5, rk6)@#i4
    & AttackerKnows(rk5)@#i5

    ==> 
        // PCS, Attacker compromised again
        (Ex rk7 #l. #i2<#l & CompromiseA(uidA, idA, uidB, idB, rk7)@l)
        // The partner was compromised and A is talking to the attacker.
    |   (Ex rk7 #l. CompromiseB(uidA, idA, uidB, idB, rk7)@l)
        // Attacker compromises the device and started a session themselves
    |   (Ex #l. #i2 < #l & CompromiseDevice(uidA, idA)@l)
    |   (Ex #l. CompromiseDevice(uidB, idB)@l)
    "

!>)

define(<!DEF7!>, <!
// Only out-of-order receives from N<=2 latest sessions.
lemma AUTOMATIC_OutOfOrderFrom2SessionsAgo: exists-trace
  "Ex cid sid1 sid2 sid3 uidA idA uidB idB rk1 rk2 rk3 rk4 rk5 #i #j #k #l #h.
   AttackerCreateDynamicStateB(cid, sid1, uidA, idA, uidB, idB, rk1) @ i &
   AttackerUpdateDynamicStateB_Sender(sid1, uidA, idA, uidB, idB, rk4, rk5) @ h &
   CreateDynamicState(sid2, uidA, idA, uidB, idB, rk2) @ j & i<j &
   CreateDynamicState(sid3, uidA, idA, uidB, idB, rk3) @ k & j<k &
   UpdateDynamicStateA_Receiver_OOO(sid1, uidA, idA, uidB, idB, rk4, rk5) @ l & k<l"
!>)

dnl Statements for base model

ifelse(BASE, true, <!
  DEF4
  
  DEF5

  DEF6
!> ,)

dnl Statements for non-resilient 1 model

ifelse(NR1, true, <!
  NEGDEF1
!>,)

dnl Statements for non-resilient 2 model

ifelse(NR2, true, <!
  NEGDEF2
!>,)

dnl Statements for resilient 1 model

ifelse(R1, true, <!
  DEF4

  DEF1

  DEF6
!>,)

dnl Statements for resilient 2 model

ifelse(R2, true, <!
  DEF4

  DEF2

  DEF6
!>,)

dnl Statements for the resilient 2 model with sequential sessions policy 

ifelse(SEQUENTIAL, true, <!
  DEF4

  DEF5

  DEF6

  DEF7
!>,)

dnl Statements for the proposal based on resilient 2

ifelse(PROPOSAL, true, <!
  DEF4

  DEF5

  DEF7
!>,)

end