m4file = AbstractModel.m4

.PHONY: all clean models base-model non-resilient-dyn-model non-resilient-static-model resilient-dyn-model resilient-static-model sequential-sessions-model proposal-model

all: models

proofs: models base-proof non-resilient-dyn-proof non-resilient-static-proof resilient-dyn-proof resilient-static-proof sequential-sessions-proof proposal-proof

base-proof: models
	tamarin-prover ./base/base.spthy --prove=AUTOMATIC\*

base-pcs: models
	tamarin-prover ./base/base.spthy --prove=ConversationPCS\*

non-resilient-dyn-proof: models
	tamarin-prover ./non-resilient-dyn/non-resilient-dyn.spthy --prove=AUTOMATIC\*

non-resilient-static-proof: models
	tamarin-prover ./non-resilient-static/non-resilient-static.spthy --prove=AUTOMATIC\*

resilient-dyn-proof: models
	tamarin-prover ./resilient-dyn/resilient-dyn.spthy --prove=AUTOMATIC\*

resilient-dyn-pcs: models
	tamarin-prover ./resilient-dyn/resilient-dyn.spthy --prove=ConversationPCS\*

resilient-static-proof: models
	tamarin-prover ./resilient-static/resilient-static.spthy --prove=AUTOMATIC\*

resilient-static-pcs: models
	tamarin-prover ./resilient-static/resilient-static.spthy --prove=ConversationPCS\*

sequential-sessions-proof: models
	tamarin-prover ./sequential/sequential.spthy --prove=AUTOMATIC\*

proposal-proof: models
	tamarin-prover ./proposal/proposal.spthy --prove=AUTOMATIC\*

tokenpassing-proof: tokenpassing.spthy
	tamarin-prover ./tokenpassing.spthy --prove=AUTOMATIC\*


models: $(m4file) base-model non-resilient-dyn-model non-resilient-static-model resilient-dyn-model resilient-static-model sequential-sessions-model proposal-model

base-model:
	mkdir -p ./base/
	m4 -D ONE_DYNAMIC=true -D BASE=true $(m4file) > ./base/base.spthy

non-resilient-dyn-model:
	mkdir -p ./non-resilient-dyn/
	m4 -D ONE_DYNAMIC=true -D DYNAMIC_STATE_LOSS=true -D NR1=true $(m4file) > ./non-resilient-dyn/non-resilient-dyn.spthy

non-resilient-static-model:
	mkdir -p ./non-resilient-static/
	m4 -D ONE_DYNAMIC=true -D STATIC_STATE_LOSS=true -D DYNAMIC_STATE_LOSS=true -D NR2=true $(m4file) > ./non-resilient-static/non-resilient-static.spthy

resilient-dyn-model:
	mkdir -p ./resilient-dyn/
	m4 -D DYNAMIC_STATE_LOSS=true -D R1=true $(m4file) > ./resilient-dyn/resilient-dyn.spthy

resilient-static-model:
	mkdir -p ./resilient-static/
	m4 -D DYNAMIC_STATE_LOSS=true -D STATIC_STATE_LOSS=true -D STATIC_STATE_RECOVERY=true -D R2=true $(m4file) > ./resilient-static/resilient-static.spthy

sequential-sessions-model:
	mkdir -p ./sequential/
	m4 -D DYNAMIC_STATE_LOSS=true -D STATIC_STATE_LOSS=true -D STATIC_STATE_RECOVERY=true -D SEQUENTIAL_SESSIONS=true -D SEQUENTIAL=true $(m4file) > ./sequential/sequential.spthy

proposal-model:
	mkdir -p ./proposal/
	m4 -D DYNAMIC_STATE_LOSS=true -D STATIC_STATE_LOSS=true -D STATIC_STATE_RECOVERY=true -D SEQUENTIAL_SESSIONS=true -D PROPOSAL=true $(m4file) > ./proposal/proposal.spthy

clean:
	rm ./base/base.spthy -f
	rm ./non-resilient-dyn/non-resilient-dyn.spthy -f
	rm ./non-resilient-static/non-resilient-static.spthy -f
	rm ./resilient-dyn/resilient-dyn.spthy -f
	rm ./resilient-static/resilient-static.spthy -f
	rm ./sequential/sequential.spthy -f
	rm ./proposal/proposal.spthy -f