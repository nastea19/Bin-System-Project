--------------------------- MODULE trash_multiple ---------------------------

EXTENDS trash_data


(* --algorithm trash_bins

\*****************************
\* Define global variables
\*****************************
variables
  \* Variables for trash bins
  outerDoorOpen = [b \in Bins |-> FALSE],
  outerDoorLocked = [b \in Bins |-> TRUE],
  trapDoorOpen = [b \in Bins |-> FALSE],
  ramExtended = [b \in Bins |-> FALSE],
  trashInTop = [b \in Bins |-> 0],
  trashCompressed = [b \in Bins |-> 0],
  trashUncompressed = [b \in Bins |-> 0],
  trashCapacity = [b \in Bins |-> MaxCapacity],
  trapDestroyed = [b \in Bins |-> FALSE],

  \* Variables for users
  userTrash = [u \in Users |-> 0],

  \* Command for bin
  \* for command "change_outer_lock", open->TRUE means unlocked and open->FALSE means locked
  \* for command "change_ram", open->TRUE means ram extended and open->FALSE means ram retracted
  binCommand = [b \in Bins |-> [command |-> "finished", open |-> FALSE]],
  \* Sensor from outer door of bin
  binSensor = [b \in Bins |-> [sensor |-> "idle"]],
  \* Central scan requests of all users
  scans = << >>,
  \* Permissions per user
  permissions = [u \in Users |-> << >>],
  \* Requests to/from server
  serverRequests = << >>,
  serverResponses = << >>,
  \* Commands for the trucks
  truckCommand = [t \in Trucks |-> [command |-> "emptied", bin |-> 1]],
  \* Tracks where each bin is in its cycle
  binPhase = [b \in Bins |-> "idle"],
  \* Truck assigned to a bin (0 = none); only meaningful in phase "await_truck"
  binTruck = [b \in Bins |-> 0],
  \* TRUE while a granted deposit is in progress at bin b (ghost variable)
  authorized = [b \in Bins |-> FALSE];

define

\*****************************
\* Helper functions
\*****************************
Trash(bin) == trashCompressed[bin] + trashUncompressed[bin]
CapacityExceeded(bin) == Trash(bin) > trashCapacity[bin]
TrashFitsCapacity(bin, trash) == Trash(bin) + trash <= trashCapacity[bin]
Full(b) == ~TrashFitsCapacity(b, MaxUserTrash)

\* Trucks that are idle and not still awaited by a bin
AvailableTrucks == {t \in Trucks :
                      /\ truckCommand[t].command = "emptied"
                      /\ \A b \in Bins : ~(binPhase[b] = "await_truck" /\ binTruck[b] = t)}

Phases == {"idle", "unlocking", "in_use", "locked", "trapdoor_open", "ram_out",
            "ram_in", "trapdoor_closed", "need_truck", "await_truck"}

\* Bin b is waiting for the control and is ready for the next step
CanAdvance(b) ==
    /\ binPhase[b] \notin {"idle", "need_truck", "await_truck"}
    /\ binCommand[b].command = "finished"
    /\ (binPhase[b] = "in_use" => binSensor[b].sensor = "outer_door_closed")

\* Bin b is full and some truck can be sent
NeedsTruck(b) == /\ binPhase[b] = "need_truck"
                 /\ AvailableTrucks /= {}

\* The truck assigned to bin b has finished emptying it
TruckFinished(b) == /\ binPhase[b] = "await_truck"
                    /\ truckCommand[binTruck[b]].command = "emptied"

\* Some bin needs the control's attention (has priority over new scans)
WorkPending == \E b \in Bins : CanAdvance(b) \/ NeedsTruck(b) \/ TruckFinished(b)


\*****************************
\* Type checks
\*****************************
TypeOK == /\ \A b \in Bins: /\ binPhase[b] \in Phases
                            /\ binTruck[b] \in Trucks \cup {0}
                            /\ authorized[b] \in BOOLEAN
                            /\ outerDoorOpen[b] \in BOOLEAN
                            /\ outerDoorLocked[b] \in BOOLEAN
                            /\ trapDoorOpen[b] \in BOOLEAN
                            /\ ramExtended[b] \in BOOLEAN
                            /\ trashInTop[b] \in Nat
                            /\ trashCompressed[b] \in Nat
                            /\ trashUncompressed[b] \in Nat
                            /\ trashCapacity[b] \in Nat
                            /\ trapDestroyed[b] \in BOOLEAN
                            /\ binCommand[b].command \in BinCommand
                            /\ binCommand[b].open \in BOOLEAN
                            /\ binSensor[b].sensor \in BinSensor
          /\ \A u \in Users: userTrash[u] \in Nat
          /\ \A i \in 1..Len(scans):
               /\ scans[i].bin \in Bins
               /\ scans[i].user \in Users
          /\ \A u \in Users:
               \A i \in 1..Len(permissions[u]):
                 /\ permissions[u][i].user \in Users
                 /\ permissions[u][i].bin \in Bins
                 /\ permissions[u][i].granted \in BOOLEAN
          /\ \A i \in 1..Len(serverRequests):
               /\ serverRequests[i].user \in Users
          /\ \A i \in 1..Len(serverResponses):
               /\ serverResponses[i].user \in Users
               /\ serverResponses[i].permission \in BOOLEAN
          /\ \A t \in Trucks: /\ truckCommand[t].command \in TruckCommand
                              /\ truckCommand[t].bin \in Bins

\* Check that message queues are not overflowing
MessagesOK == /\ Len(scans) <= NumUsers
              /\ \A u \in Users:
                   Len(permissions[u]) <= 1
              /\ Len(serverRequests) <= 1
              /\ Len(serverResponses) <= 1


\*****************************
\* Sanity checks
\*****************************
CapacitiesRespected == \A b \in Bins:
                         /\ trashUncompressed[b] >= 0
                         /\ trashUncompressed[b] <= trashCapacity[b]
                         /\ trashCompressed[b] >= 0
                         /\ trashCompressed[b] <= trashCapacity[b]
                         /\ trashCapacity[b] >= 0
                         /\ trashCapacity[b] <= MaxCapacity
TrapNotDestroyed == \A b \in Bins:
                      ~trapDestroyed[b]
CapacityNotExceeded == \A b \in Bins:
                         ~CapacityExceeded(b)


\*****************************
\* Properties of interest
\*****************************
\* Safety
OuterDoorLocked == \A b \in Bins: outerDoorLocked[b] => ~outerDoorOpen[b]
RamOuterDoor == \A b \in Bins: ramExtended[b] => (~outerDoorOpen[b] /\ outerDoorLocked[b])
AuthorizedOpenOnly == \A b \in Bins: outerDoorOpen[b] => authorized[b]

\* Liveness
TrashEmptied == \A b \in Bins: (Full(b) ~> ~Full(b))
UserTrash == \A u \in Users: ([]<>(userTrash[u] > 0) /\ []<>(userTrash[u] = 0))
UserTrashDeposited == \A u \in Users: ((userTrash[u] > 0) ~> (userTrash[u] = 0))
TruckEmpties == \A b \in Bins, t \in Trucks:
                  ((truckCommand[t].command = "request" /\ truckCommand[t].bin = b)
                   ~> (truckCommand[t].command = "emptied"))

end define;


\*****************************
\* Helper macros
\*****************************

\* Compress trash
macro compress(compressed, uncompressed) begin
  compressed := compressed + IF (uncompressed > 1) THEN uncompressed \div 2 ELSE uncompressed;
  uncompressed := 0;
end macro

\* Read res from queue.
\* The macro awaits a non-empty queue.
macro read(queue, res) begin
  await queue /= <<>>;
  res := Head(queue);
  queue := Tail(queue);
end macro

\* Write msg to the queue.
macro write(queue, msg) begin
  queue := Append(queue, msg);
end macro


\*****************************
\* Process for a bin
\*****************************
fair process binProcess \in Bins
begin
  BinWaitForCommand:
    while TRUE do
      await binCommand[self].command /= "finished";
      if binCommand[self].command = "change_outer_door" then
        assert ~outerDoorLocked[self];
        outerDoorOpen[self] := binCommand[self].open;
        if ~outerDoorOpen[self] then
          binSensor[self] := [sensor |-> "outer_door_closed"];
        end if
      elsif binCommand[self].command = "change_outer_lock" then
        assert ~outerDoorOpen[self];
        outerDoorLocked[self] := ~(binCommand[self].open);
      elsif binCommand[self].command = "change_trap_door" then
        assert outerDoorLocked[self];
        if ramExtended[self] \/ CapacityExceeded(self) then
            trapDestroyed[self] := TRUE;
        end if;
        trapDoorOpen[self] := binCommand[self].open;
        if trapDoorOpen[self] then
          trashUncompressed[self] := trashUncompressed[self] + trashInTop[self];
          trashInTop[self] := 0;
        end if
      elsif binCommand[self].command = "change_ram" then
        assert outerDoorLocked[self];
        ramExtended[self] := binCommand[self].open;
        if ramExtended[self] then
          if ~trapDoorOpen[self] then
            trapDestroyed[self] := TRUE;
          end if;
          compress(trashCompressed[self], trashUncompressed[self]);
        end if;
      elsif binCommand[self].command = "empty" then
        assert outerDoorLocked[self];
        assert ~trapDoorOpen[self];
        assert ~ramExtended[self];
        assert trashInTop[self] = 0;
        assert trashUncompressed[self] = 0;
        trashCompressed[self] := 0;
      else
        assert FALSE;
      end if;
  BinCommandFinished:
      binCommand[self].command := "finished";
    end while;
end process;


\*****************************
\* Process for a user
\*****************************
fair process userProcess \in Users
variables
  perm = [user |-> 0, bin |-> 0, granted |-> FALSE],
  selectedBin = 0
begin
  UserNextIteration:
    while TRUE do
      if userTrash[self] = 0 then
  UserNewTrash:
        with amt \in 1..MaxUserTrash do
          userTrash[self] := amt;
        end with;
      end if;
  UserScanCard:
      with sBin \in Bins do
        selectedBin := sBin;
        write(scans, [user |-> self, bin |-> selectedBin]);
      end with;
  UserAwaitScanResponse:
      read(permissions[self], perm);
      assert perm.user = self;
      assert perm.bin = selectedBin;
      if perm.granted then
  UserOpenDoor:
        binCommand[selectedBin] := [command |-> "change_outer_door", open |-> TRUE];
  UserAwaitOpenDoor:
        await binCommand[selectedBin].command = "finished";
  UserDepositTrash:
        assert trashInTop[selectedBin] = 0;
        trashInTop[selectedBin] := userTrash[self];
        userTrash[self] := 0;
  UserCloseDoor:
        binCommand[selectedBin] := [command |-> "change_outer_door", open |-> FALSE];
  UserAwaitClosedDoor:
        await binCommand[selectedBin].command = "finished";
      end if;
    end while;
end process;


\*****************************
\* Process for a server
\*****************************
fair process serverProcess = Server
variables
  req = [user |-> 0]
begin
  ServerNextIteration:
    while TRUE do
  ServerAwaitRequest:
      read(serverRequests, req);
      with valid \in ValidCard(req.user) do
        write(serverResponses, [user |-> req.user, permission |-> valid]);
      end with;
    end while;
end process;


\*****************************
\* Process for a truck
\*****************************
\* Waits for a request addressed to this truck (own slot in truckCommand),
\* drives to the requested bin, empties it, reports back.
fair process truckProcess \in Trucks
begin
  TruckWait:
    while TRUE do
      await truckCommand[self].command = "request";
      truckCommand[self].command := "arrived";
  TruckEmpty:
      await binCommand[truckCommand[self].bin].command = "finished";
      binCommand[truckCommand[self].bin] := [command |-> "empty", open |-> FALSE];
  TruckDone:
      await binCommand[truckCommand[self].bin].command = "finished";
      truckCommand[self] := [command |-> "emptied", bin |-> 1];
    end while;
end process;


\*****************************
\* Process for the controller
\*****************************
\* Each iteration the control does ONE of:
\* 1.handle a scan (only if no bin needs attention),
\* 2.advance one bin through its deposit cycle,
\* 3.dispatch an available truck to a full bin,
\* 4.release a bin whose truck has finished.
\* Bin/truck work has priority over scans so that weak fairness of the
\* control process cannot starve truck dispatching.
fair process controlProcess = Control
variables
    scan = [user |-> 0, bin |-> 1],
    binUser = [b \in Bins |-> 0];
begin
    ControlLoop:
        while TRUE do
            either
                \* (1) Handle the next scan
                await ~WorkPending;
                read(scans, scan);
                write(serverRequests, [user |-> scan.user]);
    ControlAwaitResponse:
                await serverResponses /= <<>>;
                if Head(serverResponses).permission
                    /\ binPhase[scan.bin] = "idle"
                    /\ binCommand[scan.bin].command = "finished"
                    /\ TrashFitsCapacity(scan.bin, MaxUserTrash) then
                    binCommand[scan.bin] := [command |-> "change_outer_lock", open |-> TRUE];
                    binUser[scan.bin] := scan.user;
                    binPhase[scan.bin] := "unlocking";
                else
                    write(permissions[scan.user], [user |-> scan.user, bin |-> scan.bin, granted |-> FALSE]);
                end if;
                serverResponses := Tail(serverResponses);
                scan := [user |-> 0, bin |-> 1];
            or
                \* (2) Advance a bin whose last command has finished
                with b \in Bins do
                    await CanAdvance(b);
                    if binPhase[b] = "unlocking" then
                        write(permissions[binUser[b]], [user |-> binUser[b], bin |-> b, granted |-> TRUE]);
                        authorized[b] := TRUE;
                        binUser[b] := 0;
                        binPhase[b] := "in_use";
                    elsif binPhase[b] = "in_use" then
                        binSensor[b] := [sensor |-> "idle"];
                        binCommand[b] := [command |-> "change_outer_lock", open |-> FALSE];
                        authorized[b] := FALSE;
                        binPhase[b] := "locked";
                    elsif binPhase[b] = "locked" then
                        binCommand[b] := [command |-> "change_trap_door", open |-> TRUE];
                        binPhase[b] := "trapdoor_open";
                    elsif binPhase[b] = "trapdoor_open" then
                        binCommand[b] := [command |-> "change_ram", open |-> TRUE];
                        binPhase[b] := "ram_out";
                    elsif binPhase[b] = "ram_out" then
                        binCommand[b] := [command |-> "change_ram", open |-> FALSE];
                        binPhase[b] := "ram_in";
                    elsif binPhase[b] = "ram_in" then
                        binCommand[b] := [command |-> "change_trap_door", open |-> FALSE];
                        binPhase[b] := "trapdoor_closed";
                    elsif binPhase[b] = "trapdoor_closed" then
                        if TrashFitsCapacity(b, MaxUserTrash) then
                            binPhase[b] := "idle";
                        else
                            binPhase[b] := "need_truck";
                        end if;
                    end if;
                end with;
            or
                \* (3) Send any available truck to a full bin
                with b \in Bins, t \in Trucks do
                    await NeedsTruck(b) /\ t \in AvailableTrucks;
                    truckCommand[t] := [command |-> "request", bin |-> b];
                    binTruck[b] := t;
                    binPhase[b] := "await_truck";
                end with;
            or
                \* (4) Truck finished: the bin can be used again
                with b \in Bins do
                    await TruckFinished(b);
                    binTruck[b] := 0;
                    binPhase[b] := "idle";
                end with;
            end either;
        end while;
end process;


end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "bdc95792" /\ chksum(tla) = "74bb495a")
VARIABLES outerDoorOpen, outerDoorLocked, trapDoorOpen, ramExtended, 
          trashInTop, trashCompressed, trashUncompressed, trashCapacity, 
          trapDestroyed, userTrash, binCommand, binSensor, scans, permissions, 
          serverRequests, serverResponses, truckCommand, binPhase, binTruck, 
          authorized, pc

(* define statement *)
Trash(bin) == trashCompressed[bin] + trashUncompressed[bin]
CapacityExceeded(bin) == Trash(bin) > trashCapacity[bin]
TrashFitsCapacity(bin, trash) == Trash(bin) + trash <= trashCapacity[bin]
Full(b) == ~TrashFitsCapacity(b, MaxUserTrash)


AvailableTrucks == {t \in Trucks :
                      /\ truckCommand[t].command = "emptied"
                      /\ \A b \in Bins : ~(binPhase[b] = "await_truck" /\ binTruck[b] = t)}

Phases == {"idle", "unlocking", "in_use", "locked", "trapdoor_open", "ram_out",
            "ram_in", "trapdoor_closed", "need_truck", "await_truck"}


CanAdvance(b) ==
    /\ binPhase[b] \notin {"idle", "need_truck", "await_truck"}
    /\ binCommand[b].command = "finished"
    /\ (binPhase[b] = "in_use" => binSensor[b].sensor = "outer_door_closed")


NeedsTruck(b) == /\ binPhase[b] = "need_truck"
                 /\ AvailableTrucks /= {}


TruckFinished(b) == /\ binPhase[b] = "await_truck"
                    /\ truckCommand[binTruck[b]].command = "emptied"


WorkPending == \E b \in Bins : CanAdvance(b) \/ NeedsTruck(b) \/ TruckFinished(b)





TypeOK == /\ \A b \in Bins: /\ binPhase[b] \in Phases
                            /\ binTruck[b] \in Trucks \cup {0}
                            /\ authorized[b] \in BOOLEAN
                            /\ outerDoorOpen[b] \in BOOLEAN
                            /\ outerDoorLocked[b] \in BOOLEAN
                            /\ trapDoorOpen[b] \in BOOLEAN
                            /\ ramExtended[b] \in BOOLEAN
                            /\ trashInTop[b] \in Nat
                            /\ trashCompressed[b] \in Nat
                            /\ trashUncompressed[b] \in Nat
                            /\ trashCapacity[b] \in Nat
                            /\ trapDestroyed[b] \in BOOLEAN
                            /\ binCommand[b].command \in BinCommand
                            /\ binCommand[b].open \in BOOLEAN
                            /\ binSensor[b].sensor \in BinSensor
          /\ \A u \in Users: userTrash[u] \in Nat
          /\ \A i \in 1..Len(scans):
               /\ scans[i].bin \in Bins
               /\ scans[i].user \in Users
          /\ \A u \in Users:
               \A i \in 1..Len(permissions[u]):
                 /\ permissions[u][i].user \in Users
                 /\ permissions[u][i].bin \in Bins
                 /\ permissions[u][i].granted \in BOOLEAN
          /\ \A i \in 1..Len(serverRequests):
               /\ serverRequests[i].user \in Users
          /\ \A i \in 1..Len(serverResponses):
               /\ serverResponses[i].user \in Users
               /\ serverResponses[i].permission \in BOOLEAN
          /\ \A t \in Trucks: /\ truckCommand[t].command \in TruckCommand
                              /\ truckCommand[t].bin \in Bins


MessagesOK == /\ Len(scans) <= NumUsers
              /\ \A u \in Users:
                   Len(permissions[u]) <= 1
              /\ Len(serverRequests) <= 1
              /\ Len(serverResponses) <= 1





CapacitiesRespected == \A b \in Bins:
                         /\ trashUncompressed[b] >= 0
                         /\ trashUncompressed[b] <= trashCapacity[b]
                         /\ trashCompressed[b] >= 0
                         /\ trashCompressed[b] <= trashCapacity[b]
                         /\ trashCapacity[b] >= 0
                         /\ trashCapacity[b] <= MaxCapacity
TrapNotDestroyed == \A b \in Bins:
                      ~trapDestroyed[b]
CapacityNotExceeded == \A b \in Bins:
                         ~CapacityExceeded(b)






OuterDoorLocked == \A b \in Bins: outerDoorLocked[b] => ~outerDoorOpen[b]
RamOuterDoor == \A b \in Bins: ramExtended[b] => (~outerDoorOpen[b] /\ outerDoorLocked[b])
AuthorizedOpenOnly == \A b \in Bins: outerDoorOpen[b] => authorized[b]


TrashEmptied == \A b \in Bins: (Full(b) ~> ~Full(b))
UserTrash == \A u \in Users: ([]<>(userTrash[u] > 0) /\ []<>(userTrash[u] = 0))
UserTrashDeposited == \A u \in Users: ((userTrash[u] > 0) ~> (userTrash[u] = 0))
TruckEmpties == \A b \in Bins, t \in Trucks:
                  ((truckCommand[t].command = "request" /\ truckCommand[t].bin = b)
                   ~> (truckCommand[t].command = "emptied"))

VARIABLES perm, selectedBin, req, scan, binUser

vars == << outerDoorOpen, outerDoorLocked, trapDoorOpen, ramExtended, 
           trashInTop, trashCompressed, trashUncompressed, trashCapacity, 
           trapDestroyed, userTrash, binCommand, binSensor, scans, 
           permissions, serverRequests, serverResponses, truckCommand, 
           binPhase, binTruck, authorized, pc, perm, selectedBin, req, scan, 
           binUser >>

ProcSet == (Bins) \cup (Users) \cup {Server} \cup (Trucks) \cup {Control}

Init == (* Global variables *)
        /\ outerDoorOpen = [b \in Bins |-> FALSE]
        /\ outerDoorLocked = [b \in Bins |-> TRUE]
        /\ trapDoorOpen = [b \in Bins |-> FALSE]
        /\ ramExtended = [b \in Bins |-> FALSE]
        /\ trashInTop = [b \in Bins |-> 0]
        /\ trashCompressed = [b \in Bins |-> 0]
        /\ trashUncompressed = [b \in Bins |-> 0]
        /\ trashCapacity = [b \in Bins |-> MaxCapacity]
        /\ trapDestroyed = [b \in Bins |-> FALSE]
        /\ userTrash = [u \in Users |-> 0]
        /\ binCommand = [b \in Bins |-> [command |-> "finished", open |-> FALSE]]
        /\ binSensor = [b \in Bins |-> [sensor |-> "idle"]]
        /\ scans = << >>
        /\ permissions = [u \in Users |-> << >>]
        /\ serverRequests = << >>
        /\ serverResponses = << >>
        /\ truckCommand = [t \in Trucks |-> [command |-> "emptied", bin |-> 1]]
        /\ binPhase = [b \in Bins |-> "idle"]
        /\ binTruck = [b \in Bins |-> 0]
        /\ authorized = [b \in Bins |-> FALSE]
        (* Process userProcess *)
        /\ perm = [self \in Users |-> [user |-> 0, bin |-> 0, granted |-> FALSE]]
        /\ selectedBin = [self \in Users |-> 0]
        (* Process serverProcess *)
        /\ req = [user |-> 0]
        (* Process controlProcess *)
        /\ scan = [user |-> 0, bin |-> 1]
        /\ binUser = [b \in Bins |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in Bins -> "BinWaitForCommand"
                                        [] self \in Users -> "UserNextIteration"
                                        [] self = Server -> "ServerNextIteration"
                                        [] self \in Trucks -> "TruckWait"
                                        [] self = Control -> "ControlLoop"]

BinWaitForCommand(self) == /\ pc[self] = "BinWaitForCommand"
                           /\ binCommand[self].command /= "finished"
                           /\ IF binCommand[self].command = "change_outer_door"
                                 THEN /\ Assert(~outerDoorLocked[self], 
                                                "Failure of assertion at line 195, column 9.")
                                      /\ outerDoorOpen' = [outerDoorOpen EXCEPT ![self] = binCommand[self].open]
                                      /\ IF ~outerDoorOpen'[self]
                                            THEN /\ binSensor' = [binSensor EXCEPT ![self] = [sensor |-> "outer_door_closed"]]
                                            ELSE /\ TRUE
                                                 /\ UNCHANGED binSensor
                                      /\ UNCHANGED << outerDoorLocked, 
                                                      trapDoorOpen, 
                                                      ramExtended, trashInTop, 
                                                      trashCompressed, 
                                                      trashUncompressed, 
                                                      trapDestroyed >>
                                 ELSE /\ IF binCommand[self].command = "change_outer_lock"
                                            THEN /\ Assert(~outerDoorOpen[self], 
                                                           "Failure of assertion at line 201, column 9.")
                                                 /\ outerDoorLocked' = [outerDoorLocked EXCEPT ![self] = ~(binCommand[self].open)]
                                                 /\ UNCHANGED << trapDoorOpen, 
                                                                 ramExtended, 
                                                                 trashInTop, 
                                                                 trashCompressed, 
                                                                 trashUncompressed, 
                                                                 trapDestroyed >>
                                            ELSE /\ IF binCommand[self].command = "change_trap_door"
                                                       THEN /\ Assert(outerDoorLocked[self], 
                                                                      "Failure of assertion at line 204, column 9.")
                                                            /\ IF ramExtended[self] \/ CapacityExceeded(self)
                                                                  THEN /\ trapDestroyed' = [trapDestroyed EXCEPT ![self] = TRUE]
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED trapDestroyed
                                                            /\ trapDoorOpen' = [trapDoorOpen EXCEPT ![self] = binCommand[self].open]
                                                            /\ IF trapDoorOpen'[self]
                                                                  THEN /\ trashUncompressed' = [trashUncompressed EXCEPT ![self] = trashUncompressed[self] + trashInTop[self]]
                                                                       /\ trashInTop' = [trashInTop EXCEPT ![self] = 0]
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED << trashInTop, 
                                                                                       trashUncompressed >>
                                                            /\ UNCHANGED << ramExtended, 
                                                                            trashCompressed >>
                                                       ELSE /\ IF binCommand[self].command = "change_ram"
                                                                  THEN /\ Assert(outerDoorLocked[self], 
                                                                                 "Failure of assertion at line 214, column 9.")
                                                                       /\ ramExtended' = [ramExtended EXCEPT ![self] = binCommand[self].open]
                                                                       /\ IF ramExtended'[self]
                                                                             THEN /\ IF ~trapDoorOpen[self]
                                                                                        THEN /\ trapDestroyed' = [trapDestroyed EXCEPT ![self] = TRUE]
                                                                                        ELSE /\ TRUE
                                                                                             /\ UNCHANGED trapDestroyed
                                                                                  /\ trashCompressed' = [trashCompressed EXCEPT ![self] = (trashCompressed[self]) + IF ((trashUncompressed[self]) > 1) THEN (trashUncompressed[self]) \div 2 ELSE (trashUncompressed[self])]
                                                                                  /\ trashUncompressed' = [trashUncompressed EXCEPT ![self] = 0]
                                                                             ELSE /\ TRUE
                                                                                  /\ UNCHANGED << trashCompressed, 
                                                                                                  trashUncompressed, 
                                                                                                  trapDestroyed >>
                                                                  ELSE /\ IF binCommand[self].command = "empty"
                                                                             THEN /\ Assert(outerDoorLocked[self], 
                                                                                            "Failure of assertion at line 223, column 9.")
                                                                                  /\ Assert(~trapDoorOpen[self], 
                                                                                            "Failure of assertion at line 224, column 9.")
                                                                                  /\ Assert(~ramExtended[self], 
                                                                                            "Failure of assertion at line 225, column 9.")
                                                                                  /\ Assert(trashInTop[self] = 0, 
                                                                                            "Failure of assertion at line 226, column 9.")
                                                                                  /\ Assert(trashUncompressed[self] = 0, 
                                                                                            "Failure of assertion at line 227, column 9.")
                                                                                  /\ trashCompressed' = [trashCompressed EXCEPT ![self] = 0]
                                                                             ELSE /\ Assert(FALSE, 
                                                                                            "Failure of assertion at line 230, column 9.")
                                                                                  /\ UNCHANGED trashCompressed
                                                                       /\ UNCHANGED << ramExtended, 
                                                                                       trashUncompressed, 
                                                                                       trapDestroyed >>
                                                            /\ UNCHANGED << trapDoorOpen, 
                                                                            trashInTop >>
                                                 /\ UNCHANGED outerDoorLocked
                                      /\ UNCHANGED << outerDoorOpen, binSensor >>
                           /\ pc' = [pc EXCEPT ![self] = "BinCommandFinished"]
                           /\ UNCHANGED << trashCapacity, userTrash, 
                                           binCommand, scans, permissions, 
                                           serverRequests, serverResponses, 
                                           truckCommand, binPhase, binTruck, 
                                           authorized, perm, selectedBin, req, 
                                           scan, binUser >>

BinCommandFinished(self) == /\ pc[self] = "BinCommandFinished"
                            /\ binCommand' = [binCommand EXCEPT ![self].command = "finished"]
                            /\ pc' = [pc EXCEPT ![self] = "BinWaitForCommand"]
                            /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                            trapDoorOpen, ramExtended, 
                                            trashInTop, trashCompressed, 
                                            trashUncompressed, trashCapacity, 
                                            trapDestroyed, userTrash, 
                                            binSensor, scans, permissions, 
                                            serverRequests, serverResponses, 
                                            truckCommand, binPhase, binTruck, 
                                            authorized, perm, selectedBin, req, 
                                            scan, binUser >>

binProcess(self) == BinWaitForCommand(self) \/ BinCommandFinished(self)

UserNextIteration(self) == /\ pc[self] = "UserNextIteration"
                           /\ IF userTrash[self] = 0
                                 THEN /\ pc' = [pc EXCEPT ![self] = "UserNewTrash"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "UserScanCard"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, userTrash, 
                                           binCommand, binSensor, scans, 
                                           permissions, serverRequests, 
                                           serverResponses, truckCommand, 
                                           binPhase, binTruck, authorized, 
                                           perm, selectedBin, req, scan, 
                                           binUser >>

UserScanCard(self) == /\ pc[self] = "UserScanCard"
                      /\ \E sBin \in Bins:
                           /\ selectedBin' = [selectedBin EXCEPT ![self] = sBin]
                           /\ scans' = Append(scans, ([user |-> self, bin |-> selectedBin'[self]]))
                      /\ pc' = [pc EXCEPT ![self] = "UserAwaitScanResponse"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binCommand, binSensor, permissions, 
                                      serverRequests, serverResponses, 
                                      truckCommand, binPhase, binTruck, 
                                      authorized, perm, req, scan, binUser >>

UserAwaitScanResponse(self) == /\ pc[self] = "UserAwaitScanResponse"
                               /\ (permissions[self]) /= <<>>
                               /\ perm' = [perm EXCEPT ![self] = Head((permissions[self]))]
                               /\ permissions' = [permissions EXCEPT ![self] = Tail((permissions[self]))]
                               /\ Assert(perm'[self].user = self, 
                                         "Failure of assertion at line 261, column 7.")
                               /\ Assert(perm'[self].bin = selectedBin[self], 
                                         "Failure of assertion at line 262, column 7.")
                               /\ IF perm'[self].granted
                                     THEN /\ pc' = [pc EXCEPT ![self] = "UserOpenDoor"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "UserNextIteration"]
                               /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                               trapDoorOpen, ramExtended, 
                                               trashInTop, trashCompressed, 
                                               trashUncompressed, 
                                               trashCapacity, trapDestroyed, 
                                               userTrash, binCommand, 
                                               binSensor, scans, 
                                               serverRequests, serverResponses, 
                                               truckCommand, binPhase, 
                                               binTruck, authorized, 
                                               selectedBin, req, scan, binUser >>

UserOpenDoor(self) == /\ pc[self] = "UserOpenDoor"
                      /\ binCommand' = [binCommand EXCEPT ![selectedBin[self]] = [command |-> "change_outer_door", open |-> TRUE]]
                      /\ pc' = [pc EXCEPT ![self] = "UserAwaitOpenDoor"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binSensor, scans, permissions, 
                                      serverRequests, serverResponses, 
                                      truckCommand, binPhase, binTruck, 
                                      authorized, perm, selectedBin, req, scan, 
                                      binUser >>

UserAwaitOpenDoor(self) == /\ pc[self] = "UserAwaitOpenDoor"
                           /\ binCommand[selectedBin[self]].command = "finished"
                           /\ pc' = [pc EXCEPT ![self] = "UserDepositTrash"]
                           /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                           trapDoorOpen, ramExtended, 
                                           trashInTop, trashCompressed, 
                                           trashUncompressed, trashCapacity, 
                                           trapDestroyed, userTrash, 
                                           binCommand, binSensor, scans, 
                                           permissions, serverRequests, 
                                           serverResponses, truckCommand, 
                                           binPhase, binTruck, authorized, 
                                           perm, selectedBin, req, scan, 
                                           binUser >>

UserDepositTrash(self) == /\ pc[self] = "UserDepositTrash"
                          /\ Assert(trashInTop[selectedBin[self]] = 0, 
                                    "Failure of assertion at line 269, column 9.")
                          /\ trashInTop' = [trashInTop EXCEPT ![selectedBin[self]] = userTrash[self]]
                          /\ userTrash' = [userTrash EXCEPT ![self] = 0]
                          /\ pc' = [pc EXCEPT ![self] = "UserCloseDoor"]
                          /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                          trapDoorOpen, ramExtended, 
                                          trashCompressed, trashUncompressed, 
                                          trashCapacity, trapDestroyed, 
                                          binCommand, binSensor, scans, 
                                          permissions, serverRequests, 
                                          serverResponses, truckCommand, 
                                          binPhase, binTruck, authorized, perm, 
                                          selectedBin, req, scan, binUser >>

UserCloseDoor(self) == /\ pc[self] = "UserCloseDoor"
                       /\ binCommand' = [binCommand EXCEPT ![selectedBin[self]] = [command |-> "change_outer_door", open |-> FALSE]]
                       /\ pc' = [pc EXCEPT ![self] = "UserAwaitClosedDoor"]
                       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                       trapDoorOpen, ramExtended, trashInTop, 
                                       trashCompressed, trashUncompressed, 
                                       trashCapacity, trapDestroyed, userTrash, 
                                       binSensor, scans, permissions, 
                                       serverRequests, serverResponses, 
                                       truckCommand, binPhase, binTruck, 
                                       authorized, perm, selectedBin, req, 
                                       scan, binUser >>

UserAwaitClosedDoor(self) == /\ pc[self] = "UserAwaitClosedDoor"
                             /\ binCommand[selectedBin[self]].command = "finished"
                             /\ pc' = [pc EXCEPT ![self] = "UserNextIteration"]
                             /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                             trapDoorOpen, ramExtended, 
                                             trashInTop, trashCompressed, 
                                             trashUncompressed, trashCapacity, 
                                             trapDestroyed, userTrash, 
                                             binCommand, binSensor, scans, 
                                             permissions, serverRequests, 
                                             serverResponses, truckCommand, 
                                             binPhase, binTruck, authorized, 
                                             perm, selectedBin, req, scan, 
                                             binUser >>

UserNewTrash(self) == /\ pc[self] = "UserNewTrash"
                      /\ \E amt \in 1..MaxUserTrash:
                           userTrash' = [userTrash EXCEPT ![self] = amt]
                      /\ pc' = [pc EXCEPT ![self] = "UserScanCard"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, binCommand, 
                                      binSensor, scans, permissions, 
                                      serverRequests, serverResponses, 
                                      truckCommand, binPhase, binTruck, 
                                      authorized, perm, selectedBin, req, scan, 
                                      binUser >>

userProcess(self) == UserNextIteration(self) \/ UserScanCard(self)
                        \/ UserAwaitScanResponse(self)
                        \/ UserOpenDoor(self) \/ UserAwaitOpenDoor(self)
                        \/ UserDepositTrash(self) \/ UserCloseDoor(self)
                        \/ UserAwaitClosedDoor(self) \/ UserNewTrash(self)

ServerNextIteration == /\ pc[Server] = "ServerNextIteration"
                       /\ pc' = [pc EXCEPT ![Server] = "ServerAwaitRequest"]
                       /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                       trapDoorOpen, ramExtended, trashInTop, 
                                       trashCompressed, trashUncompressed, 
                                       trashCapacity, trapDestroyed, userTrash, 
                                       binCommand, binSensor, scans, 
                                       permissions, serverRequests, 
                                       serverResponses, truckCommand, binPhase, 
                                       binTruck, authorized, perm, selectedBin, 
                                       req, scan, binUser >>

ServerAwaitRequest == /\ pc[Server] = "ServerAwaitRequest"
                      /\ serverRequests /= <<>>
                      /\ req' = Head(serverRequests)
                      /\ serverRequests' = Tail(serverRequests)
                      /\ \E valid \in ValidCard(req'.user):
                           serverResponses' = Append(serverResponses, ([user |-> req'.user, permission |-> valid]))
                      /\ pc' = [pc EXCEPT ![Server] = "ServerNextIteration"]
                      /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                      trapDoorOpen, ramExtended, trashInTop, 
                                      trashCompressed, trashUncompressed, 
                                      trashCapacity, trapDestroyed, userTrash, 
                                      binCommand, binSensor, scans, 
                                      permissions, truckCommand, binPhase, 
                                      binTruck, authorized, perm, selectedBin, 
                                      scan, binUser >>

serverProcess == ServerNextIteration \/ ServerAwaitRequest

TruckWait(self) == /\ pc[self] = "TruckWait"
                   /\ truckCommand[self].command = "request"
                   /\ truckCommand' = [truckCommand EXCEPT ![self].command = "arrived"]
                   /\ pc' = [pc EXCEPT ![self] = "TruckEmpty"]
                   /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                   trapDoorOpen, ramExtended, trashInTop, 
                                   trashCompressed, trashUncompressed, 
                                   trashCapacity, trapDestroyed, userTrash, 
                                   binCommand, binSensor, scans, permissions, 
                                   serverRequests, serverResponses, binPhase, 
                                   binTruck, authorized, perm, selectedBin, 
                                   req, scan, binUser >>

TruckEmpty(self) == /\ pc[self] = "TruckEmpty"
                    /\ binCommand[truckCommand[self].bin].command = "finished"
                    /\ binCommand' = [binCommand EXCEPT ![truckCommand[self].bin] = [command |-> "empty", open |-> FALSE]]
                    /\ pc' = [pc EXCEPT ![self] = "TruckDone"]
                    /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                    trapDoorOpen, ramExtended, trashInTop, 
                                    trashCompressed, trashUncompressed, 
                                    trashCapacity, trapDestroyed, userTrash, 
                                    binSensor, scans, permissions, 
                                    serverRequests, serverResponses, 
                                    truckCommand, binPhase, binTruck, 
                                    authorized, perm, selectedBin, req, scan, 
                                    binUser >>

TruckDone(self) == /\ pc[self] = "TruckDone"
                   /\ binCommand[truckCommand[self].bin].command = "finished"
                   /\ truckCommand' = [truckCommand EXCEPT ![self] = [command |-> "emptied", bin |-> 1]]
                   /\ pc' = [pc EXCEPT ![self] = "TruckWait"]
                   /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                   trapDoorOpen, ramExtended, trashInTop, 
                                   trashCompressed, trashUncompressed, 
                                   trashCapacity, trapDestroyed, userTrash, 
                                   binCommand, binSensor, scans, permissions, 
                                   serverRequests, serverResponses, binPhase, 
                                   binTruck, authorized, perm, selectedBin, 
                                   req, scan, binUser >>

truckProcess(self) == TruckWait(self) \/ TruckEmpty(self)
                         \/ TruckDone(self)

ControlLoop == /\ pc[Control] = "ControlLoop"
               /\ \/ /\ ~WorkPending
                     /\ scans /= <<>>
                     /\ scan' = Head(scans)
                     /\ scans' = Tail(scans)
                     /\ serverRequests' = Append(serverRequests, ([user |-> scan'.user]))
                     /\ pc' = [pc EXCEPT ![Control] = "ControlAwaitResponse"]
                     /\ UNCHANGED <<binCommand, binSensor, permissions, truckCommand, binPhase, binTruck, authorized, binUser>>
                  \/ /\ \E b \in Bins:
                          /\ CanAdvance(b)
                          /\ IF binPhase[b] = "unlocking"
                                THEN /\ permissions' = [permissions EXCEPT ![binUser[b]] = Append((permissions[binUser[b]]), ([user |-> binUser[b], bin |-> b, granted |-> TRUE]))]
                                     /\ authorized' = [authorized EXCEPT ![b] = TRUE]
                                     /\ binUser' = [binUser EXCEPT ![b] = 0]
                                     /\ binPhase' = [binPhase EXCEPT ![b] = "in_use"]
                                     /\ UNCHANGED << binCommand, binSensor >>
                                ELSE /\ IF binPhase[b] = "in_use"
                                           THEN /\ binSensor' = [binSensor EXCEPT ![b] = [sensor |-> "idle"]]
                                                /\ binCommand' = [binCommand EXCEPT ![b] = [command |-> "change_outer_lock", open |-> FALSE]]
                                                /\ authorized' = [authorized EXCEPT ![b] = FALSE]
                                                /\ binPhase' = [binPhase EXCEPT ![b] = "locked"]
                                           ELSE /\ IF binPhase[b] = "locked"
                                                      THEN /\ binCommand' = [binCommand EXCEPT ![b] = [command |-> "change_trap_door", open |-> TRUE]]
                                                           /\ binPhase' = [binPhase EXCEPT ![b] = "trapdoor_open"]
                                                      ELSE /\ IF binPhase[b] = "trapdoor_open"
                                                                 THEN /\ binCommand' = [binCommand EXCEPT ![b] = [command |-> "change_ram", open |-> TRUE]]
                                                                      /\ binPhase' = [binPhase EXCEPT ![b] = "ram_out"]
                                                                 ELSE /\ IF binPhase[b] = "ram_out"
                                                                            THEN /\ binCommand' = [binCommand EXCEPT ![b] = [command |-> "change_ram", open |-> FALSE]]
                                                                                 /\ binPhase' = [binPhase EXCEPT ![b] = "ram_in"]
                                                                            ELSE /\ IF binPhase[b] = "ram_in"
                                                                                       THEN /\ binCommand' = [binCommand EXCEPT ![b] = [command |-> "change_trap_door", open |-> FALSE]]
                                                                                            /\ binPhase' = [binPhase EXCEPT ![b] = "trapdoor_closed"]
                                                                                       ELSE /\ IF binPhase[b] = "trapdoor_closed"
                                                                                                  THEN /\ IF TrashFitsCapacity(b, MaxUserTrash)
                                                                                                             THEN /\ binPhase' = [binPhase EXCEPT ![b] = "idle"]
                                                                                                             ELSE /\ binPhase' = [binPhase EXCEPT ![b] = "need_truck"]
                                                                                                  ELSE /\ TRUE
                                                                                                       /\ UNCHANGED binPhase
                                                                                            /\ UNCHANGED binCommand
                                                /\ UNCHANGED << binSensor, 
                                                                authorized >>
                                     /\ UNCHANGED << permissions, binUser >>
                     /\ pc' = [pc EXCEPT ![Control] = "ControlLoop"]
                     /\ UNCHANGED <<scans, serverRequests, truckCommand, binTruck, scan>>
                  \/ /\ \E b \in Bins:
                          \E t \in Trucks:
                            /\ NeedsTruck(b) /\ t \in AvailableTrucks
                            /\ truckCommand' = [truckCommand EXCEPT ![t] = [command |-> "request", bin |-> b]]
                            /\ binTruck' = [binTruck EXCEPT ![b] = t]
                            /\ binPhase' = [binPhase EXCEPT ![b] = "await_truck"]
                     /\ pc' = [pc EXCEPT ![Control] = "ControlLoop"]
                     /\ UNCHANGED <<binCommand, binSensor, scans, permissions, serverRequests, authorized, scan, binUser>>
                  \/ /\ \E b \in Bins:
                          /\ TruckFinished(b)
                          /\ binTruck' = [binTruck EXCEPT ![b] = 0]
                          /\ binPhase' = [binPhase EXCEPT ![b] = "idle"]
                     /\ pc' = [pc EXCEPT ![Control] = "ControlLoop"]
                     /\ UNCHANGED <<binCommand, binSensor, scans, permissions, serverRequests, truckCommand, authorized, scan, binUser>>
               /\ UNCHANGED << outerDoorOpen, outerDoorLocked, trapDoorOpen, 
                               ramExtended, trashInTop, trashCompressed, 
                               trashUncompressed, trashCapacity, trapDestroyed, 
                               userTrash, serverResponses, perm, selectedBin, 
                               req >>

ControlAwaitResponse == /\ pc[Control] = "ControlAwaitResponse"
                        /\ serverResponses /= <<>>
                        /\ IF Head(serverResponses).permission
                               /\ binPhase[scan.bin] = "idle"
                               /\ binCommand[scan.bin].command = "finished"
                               /\ TrashFitsCapacity(scan.bin, MaxUserTrash)
                              THEN /\ binCommand' = [binCommand EXCEPT ![scan.bin] = [command |-> "change_outer_lock", open |-> TRUE]]
                                   /\ binUser' = [binUser EXCEPT ![scan.bin] = scan.user]
                                   /\ binPhase' = [binPhase EXCEPT ![scan.bin] = "unlocking"]
                                   /\ UNCHANGED permissions
                              ELSE /\ permissions' = [permissions EXCEPT ![scan.user] = Append((permissions[scan.user]), ([user |-> scan.user, bin |-> scan.bin, granted |-> FALSE]))]
                                   /\ UNCHANGED << binCommand, binPhase, 
                                                   binUser >>
                        /\ serverResponses' = Tail(serverResponses)
                        /\ scan' = [user |-> 0, bin |-> 1]
                        /\ pc' = [pc EXCEPT ![Control] = "ControlLoop"]
                        /\ UNCHANGED << outerDoorOpen, outerDoorLocked, 
                                        trapDoorOpen, ramExtended, trashInTop, 
                                        trashCompressed, trashUncompressed, 
                                        trashCapacity, trapDestroyed, 
                                        userTrash, binSensor, scans, 
                                        serverRequests, truckCommand, binTruck, 
                                        authorized, perm, selectedBin, req >>

controlProcess == ControlLoop \/ ControlAwaitResponse

Next == serverProcess \/ controlProcess
           \/ (\E self \in Bins: binProcess(self))
           \/ (\E self \in Users: userProcess(self))
           \/ (\E self \in Trucks: truckProcess(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Bins : WF_vars(binProcess(self))
        /\ \A self \in Users : WF_vars(userProcess(self))
        /\ WF_vars(serverProcess)
        /\ \A self \in Trucks : WF_vars(truckProcess(self))
        /\ WF_vars(controlProcess)

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Tue Oct 20 13:06:25 CEST 2026 by nasteapopova
\* Last modified Thu Oct 15 20:11:12 CEST 2026 by kreme
