COQ_FOLDER=../coq
TEZOS_FOLDER=../../Tezos/gitlab/tezos

default:
	ruby make.rb $(COQ_FOLDER)/kernel $(TEZOS_FOLDER)/src/proto_alpha/lib_protocol $(TEZOS_FOLDER)/generated

serve:
	ruby -run -e httpd . -p 8080

watch:
	while inotifywait `find . -name "*.*rb"`; do make; done
