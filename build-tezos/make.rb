require 'open3'

tezos_folder = "../../../Tezos/gitlab/tezos"
protocol_folder = "#{tezos_folder}/src/proto_alpha/lib_protocol"
interface_file = "#{tezos_folder}/generated/Environment_mli.v"
environment_file = "Environment.v"

def copy_if_different(source, target)
  unless File.exist?(target) && File.read(source) == File.read(target) then
    system("cp #{source} #{target}")
  end
end

copy_if_different(interface_file, environment_file)
for source_name in Dir.glob("#{protocol_folder}/*.v") do
  copy_if_different(source_name, File.basename(source_name))
end

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
