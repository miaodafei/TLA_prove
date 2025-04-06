-------------------------------- MODULE raftsnapshot --------------------------------
\* This is the formal specification for the Raft consensus algorithm.
\*
\* Copyright 2014 Diego Ongaro.
\* This work is licensed under the Creative Commons Attribution-4.0
\* International License https://creativecommons.org/licenses/by/4.0/

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* The set of server IDs
CONSTANTS Server

\* The set of requests that can go into the log
CONSTANTS Value

\* Server states.
CONSTANTS Follower, Candidate, Leader

\* A reserved value.
CONSTANTS Nil

\* 每一轮拷贝的日志index数目
CONSTANTS copyIndeiesPerLoop

\* Message types:
CONSTANTS RequestVoteRequest, RequestVoteResponse,
          AppendEntriesRequest, AppendEntriesResponse,
          InstallSnapshotRequest, InstallSnapshotResponse,
          IncrementalLogPutRequest, IncrementalLogPutResponse,
          FigerPrintCheckRequest, FigerPrintCheckResponse
----

VARIABLE lastAction
\* Global variables

\* A bag of records representing requests and responses sent from one server
\* to another. TLAPS doesn't support the Bags module, so this is a function
\* mapping Message to Nat.
VARIABLE messages

\* A history variable used in the proof. This would not be present in an
\* implementation.
\* Keeps track of successful elections, including the initial logs of the
\* leader and voters' logs. Set of functions containing various things about
\* successful elections (see BecomeLeader).
VARIABLE elections

\* A history variable used in the proof. This would not be present in an
\* implementation.
\* Keeps track of every log ever in the system (set of logs).
VARIABLE allLogs, appliedLogs

----
\* The following variables are all per server (functions with domain Server).

\* The server's term number.
VARIABLE currentTerm
\* The server's state (Follower, Candidate, or Leader).
VARIABLE state
\* The candidate the server voted for in its current term, or
\* Nil if it hasn't voted for any.
VARIABLE votedFor
serverVars == <<currentTerm, state, votedFor>>

\* A Sequence of log entries. The index into this sequence is the index of the
\* log entry. Unfortunately, the Sequence module defines Head(s) as the entry
\* with index 1, so be careful not to use that!
VARIABLE log
\* The index of the latest entry in the log the state machine may apply.
VARIABLE commitIndex
logVars == <<log, commitIndex>>

\* stateMachine状态机，结构为{k : Nat, v : STRING}为一个kv集合
\* snapShot本质上结构同stateMachine一致，因为实现里他就是某个时刻stateMachine的持久化备份，即使存储形式不同，他的状态也相同
\* snapShotIndex暂时未用，准备给算法用的，用来标记某一批的处理
\* copyIndex表示snapshotinstall的进度
VARIABLES stateMachine, snapShot, lastAppliedIndex, copyIndex, snapshotIndex, applyStop, diffData
SMVars == <<stateMachine, snapShot, lastAppliedIndex, appliedLogs, copyIndex, snapshotIndex, applyStop, diffData>>

\* The following variables are used only on candidates:
\* The set of servers from which the candidate has received a RequestVote
\* response in its currentTerm.
VARIABLE votesResponded
\* The set of servers from which the candidate has received a vote in its
\* currentTerm.
VARIABLE votesGranted
\* A history variable used in the proof. This would not be present in an
\* implementation.
\* Function from each server that voted for this candidate in its currentTerm
\* to that voter's log.
VARIABLE voterLog
candidateVars == <<votesResponded, votesGranted, voterLog>>

\* The following variables are used only on leaders:
\* The next entry to send to each follower.
VARIABLE nextIndex
\* The latest entry that each follower has acknowledged is the same as the
\* leader's. This is used to calculate commitIndex on the leader.
VARIABLE matchIndex
leaderVars == <<nextIndex, matchIndex, elections>>

\* End of per server variables.
----

\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<messages, allLogs, serverVars, candidateVars, leaderVars, logVars, SMVars, appliedLogs, lastAction>>

\* 我理解整个TLA+的证明本质为一个抽象能力，这个抽象能力要求你把整个架构的模块抽象为一个个的状态，raft证明中vars即为整体状态
\* Init为整体状态设计了一个初始值
\* Next则涉及列动作，这些动作涉及所有vars中某些元素状态的改变
\* 最后根据Init和Next，通过BFS可以将vars状态的改变行程一个状态图，每个节点为不同的状态，每个状态可由多种路径到达，每个能到达的路径就是一种情况
\* model，根据状态设置一些恒等的条件，比如raft consistency可以转化为vars中的某个条件
\* 这样BFS遍历所有可能状态时，会对这些条件进行检查，如果不符合则输出状态路径

\* 目前抽象能力有限，只能从大佬的证明中学习，比如raft，把消息抽象为一个msg的集合，发送消息则为添加一个消息到此集合中，接收消息则为从此集合中取出

----
\* Helpers

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

\* Helper for Send and Reply. Given a message m and bag of messages, return a
\* new bag of messages with one more m in it.
WithMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = msgs[m] + 1]
    ELSE
        msgs @@ (m :> 1)

\* Helper for Discard and Reply. Given a message m and bag of messages, return
\* a new bag of messages with one less m in it.
WithoutMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        IF msgs[m] <= 1 THEN [i \in DOMAIN msgs \ {m} |-> msgs[i]]
        ELSE [msgs EXCEPT ![m] = msgs[m] - 1]
    ELSE
        msgs

\* Add a message to the bag of messages.
Send(m) == messages' = WithMessage(m, messages)

\* Remove a message from the bag of messages. Used when a server is done
\* processing a message.
Discard(m) == messages' = WithoutMessage(m, messages)

\* Combination of Send and Discard
Reply(response, request) ==
    messages' = WithoutMessage(request, WithMessage(response, messages))

\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

LogPull(i, index) == 
    IF index - lastAppliedIndex[i] <= Len(log[i]) THEN 
        LET new == SubSeq(log[i], index - lastAppliedIndex[i], Len(log[i]))
            appliedLog == SubSeq(log[i], lastAppliedIndex[i], index - lastAppliedIndex[i])
        IN  log' = [log EXCEPT ![i] = new]
            /\ appliedLogs ' = [appliedLogs EXCEPT ![i] = appliedLog] \*apply的日志追加记录，用于一致性证明
    ELSE 
        log' = [log EXCEPT ![i] = << >>]

\* SnapshotPut(i) ==
\*     snapShot' = [snapShot EXCEPT ![i] = stateMachine[i]]
\*     /\ LogPull(log[i], lastAppliedIndex)

SnapshotPut(i, j) ==
    \* 拷贝快照点到apply点新增的日志(可能由快照安装并发的apply操作导致apply比快照前)
    LET logdata == SubSeq(log[i], snapshotIndex[i], lastAppliedIndex[i])
    IN 
    \* 只有日志传输失败了也无妨，直接重试即可
        applyStop' = 1
        /\ Send([mtype         |-> IncrementalLogPutRequest,
                mterm          |-> currentTerm[i],
                \* mlog is used as a history variable for the proof.
                \* It would not exist in a real implementation.
                mlog           |-> log[i],
                mincrementalog |-> logdata,
                msource        |-> i,
                mdest          |-> j])
        /\ UNCHANGED <<serverVars, candidateVars, leaderVars, commitIndex>>
----
\* Define initial values for all variables

InitHistoryVars == /\ elections  = {}
                   /\ allLogs    = {}
                   /\ appliedLogs = [i \in Server |-> << >>]
                   /\ voterLog   = [i \in Server |-> [j \in {} |-> <<>>]]
                   /\ lastAction = "init"
InitServerVars == /\ currentTerm = [i \in Server |-> 1]
                  /\ state       = [i \in Server |-> Follower]
                  /\ votedFor    = [i \in Server |-> Nil]
InitCandidateVars == /\ votesResponded = [i \in Server |-> {}]
                     /\ votesGranted   = [i \in Server |-> {}]
\* The values nextIndex[i][i] and matchIndex[i][i] are never read, since the
\* leader does not send itself messages. It's still easier to include these
\* in the functions.
\* stateMachine, snapShot, lastAppliedIndex, snapShotIndex
InitLeaderVars == /\ nextIndex  = [i \in Server |-> [j \in Server |-> 1]]
                  /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
InitLogVars == /\ log          = [i \in Server |-> << >>]
               /\ commitIndex  = [i \in Server |-> 0]
InitSMVars == 
    /\ stateMachine     = [i \in Server |-> << >>]
    /\ snapShot         = [i \in Server |-> << >>]
    /\ lastAppliedIndex = [i \in Server |-> 0]
    /\ copyIndex        = [i \in Server |-> 0]
    /\ snapshotIndex    = [i \in Server |-> 0]
    /\ applyStop = 0
Init == /\ messages = [m \in {} |-> 0]
        /\ InitHistoryVars
        /\ InitServerVars
        /\ InitCandidateVars
        /\ InitLeaderVars
        /\ InitLogVars
        /\ InitSMVars

----
\* Define state transitions

\* Server i restarts from stable storage.
\* It loses everything but its currentTerm, votedFor, and log.
Restart(i) ==
    /\ state'          = [state EXCEPT ![i] = Follower]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
    /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
    /\ nextIndex'      = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
    /\ matchIndex'     = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ commitIndex'    = [commitIndex EXCEPT ![i] = 0]
    /\ lastAction' = "Restart"
    /\ UNCHANGED <<messages, currentTerm, votedFor, log, elections, SMVars>>

\* Server i times out and starts a new election.
Timeout(i) == /\ state[i] \in {Follower, Candidate}
              /\ state' = [state EXCEPT ![i] = Candidate]
              /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
              \* Most implementations would probably just set the local vote
              \* atomically, but messaging localhost for it is weaker.
              /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
              /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
              /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
              /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
              /\ lastAction' = "Timeout"
              /\ UNCHANGED <<messages, leaderVars, logVars, SMVars>>

\* Candidate i sends j a RequestVote request.
RequestVote(i, j) ==
    /\ state[i] = Candidate
    /\ j \notin votesResponded[i]
    /\ votedFor' = [votedFor EXCEPT ![i] = i]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = votesGranted[i] \cup {i}]
    /\ Send([mtype         |-> RequestVoteRequest,
             mterm         |-> currentTerm[i],
             mlastLogTerm  |-> LastTerm(log[i]),
             mlastLogIndex |-> Len(log[i]) + lastAppliedIndex[i],
             msource       |-> i,
             mdest         |-> j])
    /\ lastAction' = "RequestVote"
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, SMVars>>

\* Leader i sends j an AppendEntries request containing up to 1 entry.
\* While implementations may want to send more than 1 at a time, this spec uses
\* just 1 because it minimizes atomic regions without loss of generality.
AppendEntries(i, j) ==
    lastAction' = "AppendEntries" /\
    /\ i /= j
    /\ state[i] = Leader
    /\ LET prevLogIndex == nextIndex[i][j] - 1
           prevLogTerm == IF prevLogIndex > 0 THEN
                              log[i][prevLogIndex - lastAppliedIndex].term
                          ELSE
                              0
           \* Send up to 1 entry, constrained by the end of the log.
           lastEntry == Min({Len(log[i]) + lastAppliedIndex[i], nextIndex[i][j]})
           entries == SubSeq(log[i], nextIndex[i][j] - lastAppliedIndex[i], lastEntry - lastAppliedIndex[i])
       IN Send([mtype          |-> AppendEntriesRequest,
                mterm          |-> currentTerm[i],
                mprevLogIndex  |-> prevLogIndex,
                mprevLogTerm   |-> prevLogTerm,
                mentries       |-> entries,
                \* mlog is used as a history variable for the proof.
                \* It would not exist in a real implementation.
                mlog           |-> log[i],
                mcommitIndex   |-> Min({commitIndex[i], lastEntry}),
                msource        |-> i,
                mdest          |-> j])
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, SMVars>>
\* TODO: ApplyEntries(i, entries)服务器i applyentries的日志条目
\* vars == <<messages, allLogs, serverVars, candidateVars, leaderVars, logVars, SMVars>>
ApplyEntries(i) ==
    lastAction' = "ApplyEntries" /\
    IF state[i] \in {Follower, Leader} THEN \* 只有Follower, Leader会apply
        \* LET applyUntil == commitIndex[i]
        \* IN
        IF commitIndex[i] > lastAppliedIndex[i] THEN
            \A idx \in lastAppliedIndex[i]..commitIndex[i] : \* 对所有需要apply的日志，去状态机中进行覆盖写 // 是否要+1
                LET key == log[i][idx - lastAppliedIndex[i]].value.k
                    val == log[i][idx - lastAppliedIndex[i]].value.v
                IN
                    IF stateMachine[i] # {} THEN
                        stateMachine' = [stateMachine EXCEPT ![i] = 
                            [entry \in stateMachine[i] |-> 
                                IF entry.k = key THEN [entry EXCEPT !.v = val] ELSE entry]] \* TODO: 不存在追加、弄清楚这一块.写文件这一部分状态机怎么回事写清楚，日志和状态机之间的关系写清楚 + TLA代码，kv的生成，文件名生成规则
                                    \* 有序需要说明
                    ELSE
                        UNCHANGED <<messages, serverVars, candidateVars, leaderVars, logVars, SMVars>>
            /\  lastAppliedIndex' = [lastAppliedIndex EXCEPT ![i] = commitIndex[i]] \*更新lastAppliedIndex
            \* 未进入快照流程,可以做日志清理,并且打快照,否则需要等快照安装流程处理，不然可能丢log
            \* TODO: 形式化描述,举例子用反证法证明，写成反证明法
            /\  IF applyStop /= 1 THEN 
                    LogPull(log[i], commitIndex[i])
                    /\ snapshotIndex' = [snapshotIndex EXCEPT ![i] = commitIndex[i]]
                ELSE
                    \* 快照安装流程，快照和日志的清理由快照安装流程处理，apply不能轻易删除日志
                    UNCHANGED <<log, snapshotIndex>>
            /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, commitIndex, snapShot>> \* 保持未变部分的状态
        ELSE 
            UNCHANGED <<messages, serverVars, candidateVars, leaderVars, logVars, SMVars>>
    ELSE
        UNCHANGED <<messages, serverVars, candidateVars, leaderVars, logVars, SMVars>>
\* TODO: InstallSnapshots(i, j, snap) i发送snap给jSnapshotPut和install要串行
FingerPrintCheck(i, j) ==
    Send([mtype  |-> FigerPrintCheckRequest,
            mterm          |-> currentTerm[i],
            msource        |-> i,
            mdest          |-> j])
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, commitIndex>>

InstallSnapshots(i, j) ==
    IF  i /= j /\ state[i] = Leader THEN
        \* 打快照
        SnapshotPut(i, j)
    ELSE
        UNCHANGED <<messages, serverVars, candidateVars, leaderVars, logVars, SMVars>>

\* Candidate i transitions to leader.
BecomeLeader(i) ==
    lastAction' = "BecomeLeader" /\
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum
    /\ state'      = [state EXCEPT ![i] = Leader]
    /\ nextIndex'  = [nextIndex EXCEPT ![i] =
                         [j \in Server |-> (Len(log[i]) + lastAppliedIndex[i] + 1)]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] =
                         [j \in Server |-> 0]]
    /\ elections'  = elections \cup
                         {[eterm     |-> currentTerm[i],
                           eleader   |-> i,
                           elog      |-> log[i],
                           evotes    |-> votesGranted[i],
                           evoterLog |-> voterLog[i]]}
    /\ UNCHANGED <<messages, currentTerm, votedFor, candidateVars, logVars, SMVars>>

\* Leader i receives a client request to add v to the log.
ClientRequest(i, v) ==
    lastAction' = "ClientRequest" /\
    /\ state[i] = Leader
    /\ LET entry == [term  |-> currentTerm[i],
                     value |-> v]
           newLog == Append(log[i], entry)
       IN  log' = [log EXCEPT ![i] = newLog]
    /\ UNCHANGED <<messages, serverVars, candidateVars,
                   leaderVars, commitIndex, SMVars>>

\* Leader i advances its commitIndex.
\* This is done as a separate step from handling AppendEntries responses,
\* in part to minimize atomic regions, and in part so that leaders of
\* single-server clusters are able to mark entries committed.
AdvanceCommitIndex(i) ==
    lastAction' = "AdvanceCommitIndex" /\
    /\ state[i] = Leader
    /\ LET \* The set of servers that agree up through index.
           Agree(index) == {i} \cup {k \in Server :
                                         matchIndex[i][k] >= index}
           \* The maximum indexes for which a quorum agrees
           agreeIndexes == {index \in 1..(Len(log[i]) + lastAppliedIndex[i]) :
                                Agree(index) \in Quorum}
           \* New value for commitIndex'[i]
           newCommitIndex ==
              IF /\ agreeIndexes /= {}
                 /\ log[i][Max(agreeIndexes) - lastAppliedIndex[i]].term = currentTerm[i]
              THEN
                  Max(agreeIndexes)
              ELSE
                  commitIndex[i]
       IN commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, log, SMVars>>

----
\* Message handlers
\* i = recipient, j = sender, m = message

\* Server i receives a RequestVote request from server j with
\* m.mterm <= currentTerm[i].
HandleRequestVoteRequest(i, j, m) ==
    LET logOk == \/ m.mlastLogTerm > LastTerm(log[i])
                 \/ /\ m.mlastLogTerm = LastTerm(log[i])
                    /\ m.mlastLogIndex >= (Len(log[i]) + lastAppliedIndex[i])
        grant == /\ m.mterm = currentTerm[i]
                 /\ logOk
                 /\ votedFor[i] \in {Nil, j}
    IN IF m.mterm <= currentTerm[i] THEN
            IF grant THEN votedFor' = [votedFor EXCEPT ![i] = j]
            ELSE UNCHANGED votedFor
            /\ Reply([mtype        |-> RequestVoteResponse,
                 mterm        |-> currentTerm[i],
                 mvoteGranted |-> grant,
                 \* mlog is used just for the `elections' history variable for
                 \* the proof. It would not exist in a real implementation.
                 mlog         |-> log[i],
                 msource      |-> i,
                 mdest        |-> j],
                 m)
       ELSE 
            UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars, SMVars>>

\* Server i receives a RequestVote response from server j with
\* m.mterm = currentTerm[i].
HandleRequestVoteResponse(i, j, m) ==
    \* This tallies votes even when the current state is not Candidate, but
    \* they won't be looked at, so it doesn't matter.
    /\ m.mterm = currentTerm[i]
    /\ votesResponded' = [votesResponded EXCEPT ![i] =
                              votesResponded[i] \cup {j}]
    /\ \/ /\ m.mvoteGranted
          /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                  votesGranted[i] \cup {j}]
          /\ voterLog' = [voterLog EXCEPT ![i] =
                              voterLog[i] @@ (j :> m.mlog)]
       \/ /\ ~m.mvoteGranted
          /\ UNCHANGED <<votesGranted, voterLog>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars, SMVars>>

\* Server i receives an AppendEntries request from server j with
\* m.mterm <= currentTerm[i]. This just handles m.entries of length 0 or 1, but
\* implementations could safely accept more by treating them the same as
\* multiple independent requests of 1 entry.
HandleAppendEntriesRequest(i, j, m) ==
    LET logOk == \/ m.mprevLogIndex = 0
                 \/ /\ m.mprevLogIndex > 0
                    /\ m.mprevLogIndex <= (Len(log[i]) + lastAppliedIndex[i])
                    /\ m.mprevLogTerm = log[i][m.mprevLogIndex - lastAppliedIndex].term
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ /\ \* reject request
                \/ m.mterm < currentTerm[i]
                \/ /\ m.mterm = currentTerm[i]
                   /\ state[i] = Follower
                   /\ \lnot logOk
             /\ Reply([mtype           |-> AppendEntriesResponse,
                       mterm           |-> currentTerm[i],
                       msuccess        |-> FALSE,
                       mmatchIndex     |-> 0,
                       msource         |-> i,
                       mdest           |-> j],
                       m)
             /\ UNCHANGED <<serverVars, logVars>>
          \/ \* return to follower state
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Candidate
             /\ state' = [state EXCEPT ![i] = Follower]
             /\ UNCHANGED <<currentTerm, votedFor, logVars, messages, SMVars>>
          \/ \* accept request
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Follower
             /\ logOk
             /\ LET index == m.mprevLogIndex + 1
                IN \/ \* already done with request
                       /\ \/ m.mentries = << >>
                          \/ /\ m.mentries /= << >>
                             /\ (Len(log[i]) + lastAppliedIndex[i]) >= index
                             /\ log[i][index - lastAppliedIndex[i]].term = m.mentries[1].term
                          \* This could make our commitIndex decrease (for
                          \* example if we process an old, duplicated request),
                          \* but that doesn't really affect anything.
                       /\ commitIndex' = [commitIndex EXCEPT ![i] =
                                              m.mcommitIndex]
                       /\ Reply([mtype           |-> AppendEntriesResponse,
                                 mterm           |-> currentTerm[i],
                                 msuccess        |-> TRUE,
                                 mmatchIndex     |-> m.mprevLogIndex +
                                                     Len(m.mentries),
                                 msource         |-> i,
                                 mdest           |-> j],
                                 m)
                       /\ UNCHANGED <<serverVars, log, SMVars>>
                   \/ \* conflict: remove 1 entry
                       /\ m.mentries /= << >>
                       /\ (Len(log[i]) + lastAppliedIndex[i]) >= index
                       /\ log[i][index - lastAppliedIndex[i]].term /= m.mentries[1].term
                       /\ LET new == [index2 \in 1..(Len(log[i]) - 1) |->
                                          log[i][index2]]
                          IN log' = [log EXCEPT ![i] = new]
                       /\ UNCHANGED <<serverVars, commitIndex, messages, SMVars>>
                   \/ \* no conflict: append entry
                       /\ m.mentries /= << >>
                       /\ (Len(log[i]) + lastAppliedIndex[i]) = m.mprevLogIndex
                       /\ log' = [log EXCEPT ![i] =
                                      Append(log[i], m.mentries[1])]
                       /\ UNCHANGED <<serverVars, commitIndex, messages, SMVars>>
       /\ UNCHANGED <<candidateVars, leaderVars, SMVars>>

\* Server i receives an AppendEntries response from server j with
\* m.mterm = currentTerm[i].
HandleAppendEntriesResponse(i, j, m) ==
    /\ m.mterm = currentTerm[i]
    /\ \/ /\ m.msuccess \* successful
          /\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = m.mmatchIndex + 1]
          /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.mmatchIndex]
          \* TODO apply直到最新的commitindex
          /\ ApplyEntries(i)
       \/ /\ \lnot m.msuccess \* not successful
            \*TODO :这里需要判断nextIndex - 1是否在log里，若不在则走snapshotInstall流程
          /\ IF m.mmatchIndex <= lastAppliedIndex THEN
                InstallSnapshots(i, j)
                /\ UNCHANGED <<serverVars, candidateVars, logVars, elections>>
             ELSE
                /\ nextIndex' = [nextIndex EXCEPT ![i][j] =
                               Max({m.mmatchIndex, 1})]
                /\ UNCHANGED <<matchIndex>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, logVars, elections>>

\* TODO HandleInstallSnapshotsRequest(i, j, m)
\* Server i receives an InstallSnapshotsRequest response from server j with
\* Send([mtype     |-> InstallSnapshotRequest,
\*                 mterm           |-> currentTerm[i],
\*                 mlastEntryIndex |-> lastEntryIndex,
\*                 mlastEntryTerm  |-> lastEntryTerm,
\*                 mshapshotData   |-> snap,
\*                 \* mlog is used as a history variable for the proof.
\*                 \* It would not exist in a real implementation.
\*                 mlog            |-> log[i],
\*                 msource         |-> i,
\*                 mdest           |-> j])
HandleInstallSnapshotsRequest(i, j, m) ==
    IF m.mterm <= currentTerm[i] THEN 
        IF m.mterm < currentTerm[i] THEN \* reject
            Reply([mtype           |-> InstallSnapshotResponse,
                   mterm           |-> currentTerm[i],
                   msuccess        |-> FALSE,
                   msource         |-> i,
                   mdest           |-> j],
                   m)
            /\ UNCHANGED <<serverVars, logVars, SMVars>>
        ELSE
            \* 快照恢复状态机,因为不会有覆盖，所以直接追加即可
            LET newStateMachine == Append(stateMachine[i], m.mshapshotData)
            IN  stateMachine' = [stateMachine EXCEPT ![i] = newStateMachine]
            /\  IF state[i] = Candidate THEN
                    state' = [state EXCEPT ![i] = Follower]
                ELSE
                    /\ Reply([  mtype           |-> InstallSnapshotResponse,
                                mterm           |-> currentTerm[i],
                                msuccess        |-> TRUE,
                                msource         |-> i,
                                mdest           |-> j],
                                m)
                    /\ UNCHANGED <<serverVars, leaderVars, candidateVars>>
    ELSE
        /\ UNCHANGED <<serverVars, leaderVars, candidateVars, logVars, elections, SMVars>>
\* Server i receives an AppendEntries response from server j with
\* m.mterm = currentTerm[i].
HandleInstallSnapshotsResponse(i, j, m) ==    
    IF m.msuccess THEN
        copyIndex' = [copyIndex EXCEPT ![i] = diffData[i] + copyIndeiesPerLoop]
    ELSE
        Discard(m)
        /\ UNCHANGED <<serverVars, candidateVars, logVars, elections, SMVars>>

\* HandleInremetalLogPutRequest(i, j, m)
HandleFingerPrintCheckRequest(i, j, m) ==
    IF m.mterm <= currentTerm[i] THEN 
        IF m.mterm < currentTerm[i] THEN \* reject
            Reply([mtype           |-> FigerPrintCheckResponse,
                   mterm           |-> currentTerm[i],
                   msuccess        |-> FALSE,
                   msource         |-> i,
                   mdest           |-> j],
                   m)
            /\ UNCHANGED <<serverVars, logVars, SMVars>>
        ELSE
            /\ Reply([mtype            |-> FigerPrintCheckResponse,
                       mterm           |-> currentTerm[i],
                       msuccess        |-> TRUE,
                       mdata           |-> stateMachine[i],
                       msource         |-> i,
                       mdest           |-> j],
                       m)
            /\ UNCHANGED <<serverVars, leaderVars, candidateVars>>
    ELSE
        /\ UNCHANGED <<serverVars, leaderVars, candidateVars, logVars, elections, SMVars>>

HandleFingerPrintCheckResponse(i, j, m) ==    
    IF m.msuccess THEN
        diffData[i] = {}
        /\ \A item \in m.mdata : 
        LET k == item.value.k
        IN
            \A item2 \in stateMachine[i] :
            LET k2 == item2.value.k
            IN
                IF k # k2 THEN
                    LET new == diffData[i] \cup {item}
                    IN
                        diffData' = [diffData EXCEPT ![i] = new]
                ELSE
        /\  InstallSnapshots(i, j)                
    ELSE
        Discard(m)
        /\ UNCHANGED <<serverVars, candidateVars, logVars, elections, SMVars>>
\* HandleInremetalLogPutRequest(i, j, m)
HandleInremetalLogPutRequest(i, j, m) ==
    IF m.mterm <= currentTerm[i] THEN 
        IF m.mterm < currentTerm[i] THEN \* reject
            Reply([mtype           |-> IncrementalLogPutResponse,
                   mterm           |-> currentTerm[i],
                   msuccess        |-> FALSE,
                   msource         |-> i,
                   mdest           |-> j],
                   m)
            /\ UNCHANGED <<serverVars, logVars, SMVars>>
        ELSE
            \* 收到合法的快照安装，清空raftlog
            log' = [log EXCEPT  ![i] = << >>]
            \* 对所有需要apply的日志，仅k也就是index<=k的操作，去状态机中进行覆盖apply，其余的不处理
            /\ \A item \in m.mincrementalog : 
                LET k == item.value.k
                    v == item.value.v
                IN
                    IF stateMachine[i] # {} THEN
                        stateMachine' = [stateMachine EXCEPT ![i] = 
                            [entry \in stateMachine[i] |-> 
                            IF entry.k <= k THEN [entry EXCEPT ![v] = v] ELSE entry]]
                            ELSE
                                stateMachine' = [stateMachine EXCEPT ![i] = << [k |-> k, v |-> v] >>]
            /\ Reply([mtype            |-> IncrementalLogPutResponse,
                       mterm           |-> currentTerm[i],
                       msuccess        |-> TRUE,
                       msource         |-> i,
                       mdest           |-> j],
                       m)
            /\ UNCHANGED <<serverVars, leaderVars, candidateVars>>
    ELSE
        /\ UNCHANGED <<serverVars, leaderVars, candidateVars, logVars, elections, SMVars>>
\* HandleInremetalLogPutResponse(i, j, m)
HandleInremetalLogPutResponse(i, j, m) ==
    IF \lnot m.msuccess THEN
        Discard(m) /\ applyStop' = 0
    ELSE
        snapshotIndex' = [snapshotIndex EXCEPT ![i] = lastAppliedIndex[i]]
        /\ LogPull(i, lastAppliedIndex)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, commitIndex>>

ChunkTransferSend(i, j, m) ==        
\* 按照copyIndeiesPerLoop发送快照，实际copyIndeiesPerLoop由用户指定
    LET coptUntil == Min({copyIndex[i] + copyIndeiesPerLoop, Len(stateMachine[i])}) \* 不能超过快照的边界
        snapdata == SubSeq(stateMachine[i], copyIndex[i], coptUntil)
    IN  IF copyIndex[i] + copyIndeiesPerLoop < Len(stateMachine[i]) THEN 
            Send([  mtype           |-> InstallSnapshotRequest,
                mterm           |-> currentTerm[i],
                mshapshotData   |-> snapdata,
                \* mlog is used as a history variable for the proof.
                \* It would not exist in a real implementation.
                mlog            |-> log[i],
                msource         |-> i,
                mdest           |-> j])
        ELSE
            applyStop' = 0 \* 无论成功或者失败，都可以解锁正常apply，因为到这里发送完增量chunk即可，applyStop只是为了避免打快照到发送chunk之间有apply操作变更了状态机
            /\ UNCHANGED <<serverVars, candidateVars, leaderVars, commitIndex>>
        
\* Any RPC with a newer term causes the recipient to advance its term first.
UpdateTerm(i, j, m) ==
    /\ m.mterm > currentTerm[i]
    /\ currentTerm'    = [currentTerm EXCEPT ![i] = m.mterm]
    /\ state'          = [state       EXCEPT ![i] = Follower]
    /\ votedFor'       = [votedFor    EXCEPT ![i] = Nil]
       \* messages is unchanged so m can be processed further.
    /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, SMVars>>

\* Responses with stale terms are ignored.
DropStaleResponse(i, j, m) ==
    /\ m.mterm < currentTerm[i]
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, SMVars>>

\* Receive a message.
Receive(m) ==
    LET i == m.mdest
        j == m.msource
    IN \* Any RPC with a newer term causes the recipient to advance
       \* its term first. Responses with stale terms are ignored.
       \/ UpdateTerm(i, j, m)
       \/ /\ m.mtype = RequestVoteRequest
          /\ HandleRequestVoteRequest(i, j, m)
       \/ /\ m.mtype = RequestVoteResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleRequestVoteResponse(i, j, m)
       \/ /\ m.mtype = AppendEntriesRequest
          /\ HandleAppendEntriesRequest(i, j, m)
       \/ /\ m.mtype = AppendEntriesResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleAppendEntriesResponse(i, j, m)
       \/ /\ m.mtype = InstallSnapshotRequest
          /\ HandleInstallSnapshotsRequest(i, j, m)
       \/ /\ m.mtype = InstallSnapshotResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleInstallSnapshotsResponse(i, j, m)
       \/ /\ m.mtype = IncrementalLogPutRequest
          /\ HandleInremetalLogPutRequest(i, j, m)
       \/ /\ m.mtype = IncrementalLogPutResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleInremetalLogPutResponse(i, j, m)
    /\ lastAction' = m.mtype
            

\* End of message handlers.
----
\* Network state transitions

\* The network duplicates a message
DuplicateMessage(m) ==
    /\ Send(m)
    /\ lastAction' = "DuplicateMessage"
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, SMVars>>

\* The network drops a message
DropMessage(m) ==
    /\ Discard(m)
    /\ lastAction' = "DropMessage"
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, SMVars>>

----
\* Defines how the variables may transition.
Next == /\ \/ \E i \in Server : Restart(i)
           \/ \E i \in Server : Timeout(i)
           \/ \E i,j \in Server : RequestVote(i, j)
           \/ \E i \in Server : BecomeLeader(i)
           \/ \E i \in Server, v \in 1..Len(Value): ClientRequest(i, Value[v])
           \/ \E i \in Server : AdvanceCommitIndex(i)
           \/ \E i,j \in Server : AppendEntries(i, j)
           \/ \E m \in DOMAIN messages : Receive(m)
           \/ \E m \in DOMAIN messages : DuplicateMessage(m)
           \/ \E m \in DOMAIN messages : DropMessage(m)
           \* History variable that tracks every log ever:
        /\ allLogs' = allLogs \cup {log[i] : i \in Server}

\* The specification must start with the initial state and transition according
\* to Next.
Spec == Init /\ [][Next]_vars

\* 持久化状态是否合法
----
TypeOk == 
    /\ \A i \in Server : state[i] \in {Follower, Candidate, Leader} \*每个节点的状态只能是Follower, Candidate, Leader之一
    /\ \A i \in Server : votedFor[i] \in Server \cup {Nil}          \* 每个节点的votedFor的值必须是Server或者Nil
    /\ \A i \in Server : votesResponded[i] \subseteq Server         \* 每个节点的votesResponded必须是Server的子集
    /\ \A i \in Server : votesGranted[i] \subseteq Server           \* 每个节点的votesGranted必须是Server的子集
\* 安全性原则

\*Lemma 1. Each server’s currentTerm monotonically increases:
\*∀ i ∈ Server :
\*currentTerm[i] ≤ currentTerm0'[i]
\*Timeout函数在next调用模型里必然是递增的，无需证明

\*Lemma 2. There is at most one leader per term:
\*∀ e,f ∈ elections :
\*e.eterm = f .eterm ⇒ e.eleader = f .eleader
LtOneLeader ==
    Cardinality({i \in Server : state[i] = Leader}) <= 1

\*Lemma 3. A leader’s log monotonically grows during its term:
\*∀ e ∈ elections :
\*currentTerm[e.leader ] = e.term ⇒
\*∀ index ∈ 1..Len(log[e.leader ]) :
\*log0 [e.leader][index] = log[e.leader][index]
\*logOk被嵌入到next规则里

\*Lemma 6. A server’s current term is always at least as large as the terms in its log:
\*∀ i ∈ Server :
\*∀ hindex ,termi ∈ log[i] :
\*term ≤ currentTerm[i]
CurTermGtLargestLog ==
    /\ \A i \in Server : currentTerm[i] >= LastTerm(log[i])
    
\*Lemma 7. The terms of entries grow monotonically in each log:
\*∀ l ∈ allLogs :
\*∀ index ∈ 1..(Len(l)−1) :
\*l[index ].term ≤ l[index +1].term

\* 一致性证明：
Index(xlogs) == 1..Len(xlogs) \* 服务器i从1..最后一条日志的index的集合
AllCommittedEntries(xlogs) == {<<n,xlogs[n]>> : n \in Index(xlogs)} \*因为log是<<>>类型不是一个集合，因此通过{}转换为一个集合，该集合每个元素表示，index为n：节点i的对应log的集合,并且有序
Consistency == \A i,j \in Server :  \*两个节点较小的commit的log集合一致，即为一致性
        \* 拼接applyiedlog和commit的Log
        LET finalLogI == appliedLogs[i] \o SubSeq(log[i], 1, commitIndex[i] - lastAppliedIndex[i])
            finalLogJ == appliedLogs[j] \o SubSeq(log[j], 1, commitIndex[j] - lastAppliedIndex[j])
        IN {e \in AllCommittedEntries(finalLogI) : e[1] \geq 0 /\ e[1] < Min({commitIndex[i] - lastAppliedIndex[i],commitIndex[j] - lastAppliedIndex[j]})} = 
        {e \in AllCommittedEntries(finalLogJ) : e[1] \geq 0 /\ e[1] < Min({commitIndex[i] - lastAppliedIndex[i],commitIndex[j] - lastAppliedIndex[j]})} \*commit的值一致
----
=============================================================================
\* Modification History
\* Last modified Sun Apr 06 15:41:22 CST 2025 by fengliyu
\* Created Sun Jan 05 22:51:33 CST 2025 by fengliyu
