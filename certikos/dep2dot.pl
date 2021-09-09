#!/usr/bin/perl -w
use Data::Compare;
use Data::Dumper;
use Graph::Directed;
use File::Basename;
use strict;

## Description
# This script generates a dependency graph between Coq files
# based on the content of a .depend file.
# The shape of a node indicate its compilation status whereas
# its color indicates in which directory it resides.
# /!\ It is currently not portable at all, as directories are hardcoded


## Usage
# Call the script on the .depend file and it will produce
# the dependency graph in dot format on stdout.
# One quick way to directly generate a PDF file [graph.dot.pdf]:
#  perl -w dep2dot.pl .depend | dot -Tpdf -o graph.dot.pdf


## Configuration of the script

# Per-directory attributes: node or background colors
my %dirattrs = (
    'mcertikos/clib' => 'lavender',
    'mcertikos/driver' => 'lightgrey',
#    'mcertikos/extraction' => 'dimgrey',
    'mcertikos/flatmem' => 'cyan',
    'mcertikos/invariants' => 'lightblue',
    'mcertikos/layerlib' => 'darkorange',
    'mcertikos/mm' => 'lightcyan',
    'mcertikos/objects' => 'lightskyblue',
    'mcertikos/policy' => 'beige',
    'mcertikos/proc' => 'violet',
    'mcertikos/script' => 'grey',
    'mcertikos/security' => 'sienna',
    'mcertikos/trap' => 'lightslateblue',
    'compcertx' => 'gold1',
    'compcert/flocq' => 'slategrey',
    'compcert' => 'yellow',
    'kernel' => 'orchid',
    'liblayers' => 'orange',
);

# Compilation attributes: node shapes and colors
my %compilattrs = (
    fresh     => 'shape=box, style=filled, fillcolor=palegreen',
    stale     => 'shape=tripleoctagon, style=filled, fillcolor=red',
    depstale  => 'shape=octagon, style=filled, fillcolor=darkorange',
    notfound  => 'shape=ellipse, style=filled, fillcolor=purple',
    error     => 'shape=star, style=filled, fillcolor=purple',
);


# Making sure all directories exist
foreach my $dir (keys %dirattrs) {
    if (! -d $dir) { die "Directory $dir does not exist"; }
}


## Parse .depends into a $graph
#
# Each node contains the following attributes:
#   dir      -- the cluster the node belongs to (depending on its directory)
#   name     -- the basename of the file
#   scrmtime -- the last modification time of the .v
#   objmtime -- the last modification time of the .vo
#   status   -- the compilation state of the file
#
# The node's name is the full qualified name (to avoid overshadowing)

my @suffixes = ('.v', '.vo', '.glob', '.v.beautified');
my $graph = Graph::Directed->new;

while (<>) {
	# Extract the components of this line
	my @dd = split(/[ :\n]+/);
	my $file = shift @dd or next;

    if (substr($file, (length $file) - 3, 3) eq ".vo") {
        foreach my $dep (@dd) {
            if (substr($dep, (length $dep) - 3, 3) eq ".vo") {
                $graph->add_edge($dep, $file);
            }
        }

        # Get the directory and source name of the target file
        my ($filename, $dir, $suffix) = fileparse($file, @suffixes);
        # Remove leading ../ from $dir if present
        if (index($dir, "../") == 0)
        { $dir = substr($dir, 3, (length $dir) - 3); };
        my $cluster = "";
        # To avoid having prefixes mask longer strings, we sort the hash
        foreach my $k (sort { length($b) <=> length($a) } keys %dirattrs) {
            if ($dir =~ /$k/) {
                $cluster = $k;
                last;
            }
        }
        # Get the info about source and oject files
        my @srcstat = stat("${dir}/${filename}.v");
        my @objstat = stat("${dir}/${filename}.vo");

        # Now we have all the information we need
        $graph->set_vertex_attribute($file, 'name', $filename);
        $graph->set_vertex_attribute($file, 'dir', $cluster);
        $graph->set_vertex_attribute($file, 'status', 'notfound');
        $graph->set_vertex_attribute($file, 'srcmtime',
                                     scalar(@srcstat) ? $srcstat[9] : 0);
        $graph->set_vertex_attribute($file, 'objmtime',
                                     scalar(@objstat) ? $objstat[9] : 0);
    }
}


# Remove self-loops before transitive reduction & topological sorting
my @V = $graph->vertices;
foreach my $v (@V) { $graph->delete_edge($v, $v); }

# Checks whether the graph is indeed a DAG
if (! $graph->is_dag) {
    die "The dependency graph is not acyclic, aborting.\n";
}

# Print some stats about the graph
print STDERR ("The inital graph has ", scalar $graph->vertices, " nodes and ",
              scalar $graph->edges," edges.\n");


# For the transitive reduction, we first compute the transitive closure
# and then check if we have patterns u -> w ->* v to remove u -> v.
# NB: using the tred tool from Graphviz is slower

my $transitive_graph = Graph::TransitiveClosure->new($graph, reflexive => 0);
foreach my $u (@V) {
    my @succ = $graph->successors($u);
    foreach my $w (@succ) {
        foreach my $v ($transitive_graph->successors($w)) {
            $graph->delete_edge($u, $v);
        }
    }
}
my @ts = $graph->topological_sort;

# Print the new size of the grpah
print STDERR ("The reduced graph has ", scalar $graph->edges," edges.\n");

# # Print sink vertices
# print STDERR "\nSink vertices:\n";
# my @sinks = $graph->successorless_vertices;
# foreach my $sink (sort @sinks) {
#     print STDERR "  $sink\n";
# }


## Update the freshness of each node, in topological order
## and keep stats about it
my $notfoundnodes = 0;
my $freshnodes = 0;
my $depstalenodes = 0;
my $stalenodes = 0;

foreach my $v (@ts) {
    if ($graph->has_vertex_attribute($v, 'name')) { # Make sure the node exists

        # Never compiled => not found
        if ($graph->get_vertex_attribute($v, 'objmtime') == 0
            or $graph->get_vertex_attribute($v, 'srcmtime') == 0) {
            $graph->set_vertex_attribute($v, 'status', 'notfound');
            $notfoundnodes++;
        }

        # Is it up-to-date?
        # 1) Are all dependencies up-to-date?
        my $depuptodate = 1;
        foreach my $k ($graph->predecessors($v)) {
            if (! ($graph->get_vertex_attribute($k, 'status') eq 'fresh')
                or $graph->get_vertex_attribute($v, 'objmtime')
                   < $graph->get_vertex_attribute($k, 'objmtime')) {
                $depuptodate = 0;
                last;
            }
        }
        # 2) Is the code older than the obj file?
        my $uptodate = $graph->get_vertex_attribute($v, 'srcmtime')
                       <= $graph->get_vertex_attribute($v, 'objmtime');

        if (! $uptodate) {
            $graph->set_vertex_attribute($v, 'status', 'stale');
            $stalenodes++;
        } elsif ($depuptodate) {
            $graph->set_vertex_attribute($v, 'status', 'fresh');
            $freshnodes++;
        } else {
            $graph->set_vertex_attribute($v, 'status', 'depstale');
            $depstalenodes++;
        }
    }
}

# Print the results
print STDERR "\nThere are:\n";
print STDERR "  $freshnodes nodes up to date;\n";
print STDERR "  $stalenodes nodes that failed to compile;\n";
print STDERR "  $depstalenodes nodes waiting for a dependency to compile;\n";
print STDERR "  $notfoundnodes nodes with no previous compilation files.\n";


## Producing output: two options: with or without clusters

# Options for the resulting graph
print "strict digraph deps {\n";
print "rankdir=LR;\n";
print "concentrate=true;\n";
# shape used for undef nodes only
print "node [style=filled,fillcolor=white,shape=star];\n";
print "packmode=cluster;\n";
print "outputMode = edgesfirst;\n";
print "overlap=true;\n";

## Option 1: Output the list of nodes, grouped per directory
############################################################

# Perform the grouping and put nodes in a hash
my %nodehash = map { $_ => [] } (keys %dirattrs);
foreach my $v (@V) {
    push(@{$nodehash{$graph->get_vertex_attribute($v, 'dir')}}, $v);
}

foreach my $k (sort { length($b) <=> length($a) } keys %dirattrs) {
    my $dirname = $k;
    $dirname =~ s/\//_/g;
    print ("subgraph cluster_", $dirname, " {\n");
    print "fontsize=60.0;\n";
    print "labeljust=\"c\";\n";
    print ("label=\"$k\";\n");
# Background color (l. 1) or color for each node (l. 2)
    print ("bgcolor=$dirattrs{$k};\n", "node [style=filled, fillcolor=white];\n");
#    print "node [style=filled,fillcolor=$dirattrs{$k}];\n";
    foreach my $v (@{$nodehash{$k}}) {
        if (! $graph->has_vertex_attribute($v, 'name')) {
            print STDERR ("Missing node $v (probably missing from the
adequate Makefile)\n");
        }
        if ($graph->get_vertex_attribute($v, 'dir') eq $k) {
            my $fattrs = $compilattrs{$graph->get_vertex_attribute($v, 'status')};
            print("\"$v\" [label=\"", $graph->get_vertex_attribute($v, 'name'),
                  "\",", $fattrs, "];\n");
        }
    }
    print "}\n";
}

## Option2: Output the list of nodes, in topological order
##########################################################

# foreach my $v (@ts) {
#     if ($graph->has_vertex_attribute($v, 'name')) {
#         my $fattrs = $compilattrs{$graph->get_vertex_attribute($v, 'status')};
#         my $dattrs = $dirattrs{$graph->get_vertex_attribute($v, 'dir')};
#         print("\"$v\" [label=\"", $graph->get_vertex_attribute($v, 'name'),
#               "\", $fattrs, fillcolor=$dattrs];\n");
#     } else {
#         print STDERR ("Missing node $v (probably missing from the
# adequate Makefile)\n");
#     }
# }

# Output the list of edges, in topological order
foreach my $source (@ts) {
    foreach my $target ($graph->successors($source)) {
        print("\"", $source, "\" -> \"", $target, "\"");
        if ($graph->get_vertex_attribute($source, 'dir')
            eq $graph->get_vertex_attribute($target, 'dir')) {
            print " [weight=100]";
        } else {
            # This is currently buggy as dot crashes with so many lhead/rhead
            # It would be great though: the graph would be much more readable
            # my $tail = $graph->get_vertex_attribute($source, 'dir');
            # $tail =~ s/\//_/g;
            # chop($tail);
            # my $head = $graph->get_vertex_attribute($target, 'dir');
            # $head =~ s/\//_/g;
            # chop($head);
            # print "[ltail=\"cluster_$tail\", rhead=\"cluster_$head\", style=bold]";
            print " [style=dotted]";
        }
        print ";\n";
    }
}

print "}\n";
