# Flooding Network Proof

This project was a talent track project in collaboration with the Cryptology group at Aarhus University.
The goal of the project was to show properties formally of the networks studied in the Distributed Systems and Security course.
The scope of this project prooved too big, and therefore only the first layer of the network was shown, the Flooding layer.

For an easy overview, the report can be read in [FloodingNetworkReport.pdf](FloodingNetworkReport.pdf).

## Proof Structure

The `Flood_Box` is the Flooding Network structure.
On this structure, two properties are shown on the output trace

- Safety ([Flood_Box_Safety.v](Flood_Box_Safety.v))
- Liveness ([Flood_Box_Liveness.v](Flood_Box_Liveness.v))

which are collected in [Flood_Box_Master.v](Flood_Box_Master.v). These properties are based on a user agreement, and an eventual delivery agreement posed on the input.

## Future Work

As mentioned, the scope of the project was initially larger, and should have contained the below stated layers.

### FIFO

The next layer is to ensure order on the messages delivered, such that messages are deliverd in the same order they are sent. This builds on top of the Floodig network, and therefore the proofs should also do so. The input remains the same, but the trace should then be altered.

### Causal Order

Next is to ensure that the *causal past* is maintained, i.e., if party 1 sends message 1, and then party 2 sends message 2 after recieving message 1, then party 3 must recieve message 1 before message 2.

### Total Order

Lastly, the final layer is to ensure that all messages arrive in the same order at all parties, i.e., if party 1 and party 2 both send a message before recieving any other message, then the order of those messages recieved at all other parties must be equal, which is not required by the caual past alone.

---

### Possible simplification

In the Casual past network, an initial approach uses sets of all affected messages, which is passed along. To make this more efficient, vector clocks counting the number of affected messages from each party is used. Crutially, in the construction presented in our course each party has two vector clocks - one for counting the casual past of the party and one for counting the delivered messages of each party.
The goal of the project was to formally show that these two are always equal, thereby allowing to rid noe of them.
