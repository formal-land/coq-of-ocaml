default:
	ruby make.rb ../coq/kernel ../../Tezos/gitlab/tezos

serve:
	ruby -run -e httpd . -p 8080

watch:
	while inotifywait `find . -name "*.*rb"`; do make; done
