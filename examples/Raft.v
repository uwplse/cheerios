Require Import StructTact.Fin.

Section Raft.

Variable N: nat.
Variable clientId : Type.
Variable input : Type.
Variable output : Type.
Variable stateMachineData : Type.

Definition term := nat.
Definition logIndex := nat.
Definition name := fin N.

Record entry := mkEntry {
                   eAt : name;
                   eClient : clientId;
                   eId : nat;
                   eIndex : logIndex;
                   eTerm : term;
                   eInput : input
                  }.

Inductive msg : Type :=
| RequestVote : term -> name -> logIndex -> term -> msg
| RequestVoteReply : term -> bool -> msg
| AppendEntries : term -> (name) -> logIndex -> term -> (list entry) -> logIndex -> msg
| AppendEntriesReply : term -> (list entry) -> bool -> msg.

Inductive raft_input : Type :=
| Timeout : raft_input
| ClientRequest : clientId -> nat -> input -> raft_input.

Inductive raft_output : Type :=
| NotLeader : clientId -> nat -> raft_output
| ClientResponse : clientId -> nat -> output -> raft_output.

Inductive serverType : Set :=
| Follower
| Candidate
| Leader.

Record raft_data :=
  mkRaft_data {
      currentTerm : term;
      votedFor : option name;
      leaderId : option name;
      log : list entry;
      commitIndex : logIndex;
      lastApplied : logIndex;
      stateMachine : stateMachineData;
      nextIndex : list (name * logIndex);
      matchIndex : list (name * logIndex);
      shouldSend : bool;
      votesReceived : list name;
      type : serverType;
      clientCache : list (clientId * (nat * output));
      electoralVictories : list (term * list name * list entry)
    }.

End Raft.
