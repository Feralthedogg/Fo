#!/usr/bin/env perl
use strict;
use warnings;
use FindBin qw($Bin);

my $impl = "$Bin/bench-selfhosted-check.bash";
exec 'bash', $impl, @ARGV
  or die "failed to exec $impl: $!\n";
