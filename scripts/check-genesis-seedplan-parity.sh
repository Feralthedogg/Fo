#!/usr/bin/env perl
use strict;
use warnings;
use File::Basename qw(basename);
use FindBin qw($Bin);
use lib "$Bin/lib";
use Fo::Scripts qw(dispatch_script);

dispatch_script(basename($0), $Bin, @ARGV);
