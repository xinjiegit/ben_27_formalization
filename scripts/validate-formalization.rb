#!/usr/bin/env ruby
# frozen_string_literal: true

require "yaml"

path = ARGV.fetch(0, "formalization.yaml")
document = YAML.safe_load(
  File.binread(path).force_encoding(Encoding::UTF_8),
  permitted_classes: [],
  permitted_symbols: [],
  aliases: false
)

abort "#{path} must contain one top-level mapping" unless document.is_a?(Hash)
abort "#{path}: version must be v0.4" unless document["version"] == "v0.4"

required_mappings = %w[project classification automation review]
missing = required_mappings.reject { |key| document[key].is_a?(Hash) }
abort "#{path}: missing mappings: #{missing.join(', ')}" unless missing.empty?

project = document.fetch("project")
abort "#{path}: project.name must be nonempty" unless project["name"].is_a?(String) && !project["name"].strip.empty?
abort "#{path}: project.authors must be nonempty" unless project["authors"].is_a?(Array) && !project["authors"].empty?
abort "#{path}: responsible_maintainers must be nonempty" unless project["responsible_maintainers"].is_a?(Array) && !project["responsible_maintainers"].empty?
abort "#{path}: project.license must be Apache-2.0" unless project["license"] == "Apache-2.0"

sources = document["sources"]
abort "#{path}: sources must be nonempty" unless sources.is_a?(Array) && !sources.empty?

placeholder_paths = []
walk = lambda do |value, location|
  case value
  when Hash
    value.each { |key, child| walk.call(child, "#{location}.#{key}") }
  when Array
    value.each_with_index { |child, index| walk.call(child, "#{location}[#{index}]") }
  when String
    placeholder_paths << location if value.lstrip.start_with?("TEMPLATE")
  end
end
walk.call(document, "$")
abort "#{path}: retained TEMPLATE values at #{placeholder_paths.join(', ')}" unless placeholder_paths.empty?

puts "#{path}: basic Palomar metadata checks passed"
