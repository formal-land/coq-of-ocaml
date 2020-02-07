require 'open3'

tezos_folder = "../../../Tezos/gitlab/tezos"
protocol_folder = "#{tezos_folder}/src/proto_alpha/lib_protocol"
interface_file = "#{tezos_folder}/generated/Environment_mli.v"
environment_file = "Environment.v"

system("cp #{interface_file} #{environment_file}")
system("cp #{protocol_folder}/*.v ./")

files = File.read("_CoqProject")
  .split("\n")
  .select {|line| line.include?(".v")}
  .select {|line| not line.include?("#")}
  .select {|line| not line.include?("Environment.v")}

nb_lines = 0
for file in files do
  nb_lines += File.read(file).split("\n").size
end

puts "Total number of expected valid lines: #{nb_lines}"
