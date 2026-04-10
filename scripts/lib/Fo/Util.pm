package Fo::Util;

use strict;
use warnings;

use Cwd qw(abs_path getcwd);
use Exporter qw(import);
use File::Basename qw(dirname);
use File::Compare qw(compare);
use File::Copy qw(copy);
use File::Find qw(find);
use File::Path qw(make_path remove_tree);
use File::Spec;
use File::Temp qw(tempdir tempfile);
use IPC::Open3 qw(open3);
use Symbol qw(gensym);

our @EXPORT = qw(
  repo_root_from
  script_path
  run_cmd
  run_cmd_capture
  run_script
  ensure_dir
  ensure_parent
  write_file
  read_file
  remove_paths
  copy_file
  copy_tree_contents
  collect_files
  compare_files
  make_tempdir
  make_tempfile
  devnull
  assert_regex
  slurp_lines
);

sub repo_root_from {
  my ($script_dir) = @_;
  return abs_path(File::Spec->catdir($script_dir, '..'));
}

sub script_path {
  my ($root, $name) = @_;
  return File::Spec->catfile($root, 'scripts', $name);
}

sub devnull {
  return File::Spec->devnull();
}

sub ensure_dir {
  my (@paths) = @_;
  for my $path (@paths) {
    next if -d $path;
    eval { make_path($path); 1 } or do {
      die "failed to create directory $path: $!" if !-d $path;
    };
  }
}

sub ensure_parent {
  my ($path) = @_;
  my $parent = dirname($path);
  return if !$parent || $parent eq '.';
  ensure_dir($parent);
}

sub write_file {
  my ($path, $content) = @_;
  ensure_parent($path);
  open my $fh, '>', $path or die "failed to write $path: $!";
  print {$fh} $content or die "failed to write $path: $!";
  close $fh or die "failed to close $path: $!";
}

sub read_file {
  my ($path) = @_;
  open my $fh, '<', $path or die "failed to read $path: $!";
  local $/;
  my $content = <$fh>;
  close $fh or die "failed to close $path: $!";
  return defined $content ? $content : '';
}

sub slurp_lines {
  my ($path) = @_;
  open my $fh, '<', $path or die "failed to read $path: $!";
  my @lines = <$fh>;
  close $fh or die "failed to close $path: $!";
  chomp @lines;
  return @lines;
}

sub remove_paths {
  for my $path (@_) {
    next if !defined $path;
    next if !-e $path && !-l $path;
    if (-d $path && !-l $path) {
      my $tries = 0;
      while (-e $path && $tries < 10) {
        my $err = [];
        eval { remove_tree($path, { error => \$err }); 1 } or do {
          my $status = system('rm', '-rf', $path);
          if ($status == 0) {
            last if !-e $path;
          }
        };
        last if !-e $path;
        $tries += 1;
        select undef, undef, undef, 0.1;
        if ($tries >= 10 && -e $path) {
          my @msgs = map { values %$_ } @$err;
          my $status = system('rm', '-rf', $path);
          last if $status == 0 && !-e $path;
          die join("\n", @msgs) . "\n" if @msgs;
          die "failed to remove $path\n";
        }
      }
      next;
    }
    unlink $path or die "failed to remove $path: $!";
  }
}

sub copy_file {
  my ($src, $dst) = @_;
  ensure_parent($dst);
  copy($src, $dst) or die "failed to copy $src to $dst: $!";
}

sub copy_tree_contents {
  my ($src, $dst) = @_;
  die "missing source directory $src" if !-d $src;
  ensure_dir($dst);
  find(
    {
      no_chdir => 1,
      wanted   => sub {
        my $path = $File::Find::name;
        return if $path eq $src;
        my $rel = File::Spec->abs2rel($path, $src);
        my $target = File::Spec->catfile($dst, $rel);
        if (-d $path) {
          ensure_dir($target);
          return;
        }
        return if !-f $path;
        copy_file($path, $target);
      },
    },
    $src,
  );
}

sub collect_files {
  my ($root) = @_;
  my @files;
  find(
    {
      no_chdir => 1,
      wanted   => sub {
        return if !-f $File::Find::name;
        my $rel = File::Spec->abs2rel($File::Find::name, $root);
        $rel =~ s{\\}{/}g;
        push @files, $rel;
      },
    },
    $root,
  );
  @files = sort @files;
  return @files;
}

sub compare_files {
  my ($left, $right) = @_;
  return compare($left, $right) == 0;
}

sub make_tempdir {
  my (%opts) = @_;
  return tempdir(CLEANUP => 0, %opts);
}

sub make_tempfile {
  my (%opts) = @_;
  return tempfile(%opts);
}

sub _run_with_context {
  my ($opts, $code) = @_;
  my $dir = $opts->{dir};
  my $cwd = defined $dir ? getcwd() : undef;
  my %saved_env = %ENV;
  my $wantarray = wantarray;
  my (@result, $result, $ok, $error);

  eval {
    if (defined $dir) {
      chdir $dir or die "failed to chdir to $dir: $!";
    }
    if ($opts->{env}) {
      while (my ($key, $value) = each %{ $opts->{env} }) {
        $ENV{$key} = $value;
      }
    }
    if ($wantarray) {
      @result = $code->();
    } else {
      $result = $code->();
    }
    $ok = 1;
    1;
  } or do {
    $error = $@ || "unknown failure";
  };

  %ENV = %saved_env;
  if (defined $cwd) {
    chdir $cwd or die "failed to restore cwd to $cwd: $!";
  }
  die $error if !$ok;
  return $wantarray ? @result : $result;
}

sub run_cmd {
  my ($opts, @cmd) = ref($_[0]) eq 'HASH' ? @_ : ({}, @_);
  die "missing command" if !@cmd;
  return _run_with_context(
    $opts,
    sub {
      if ($opts->{quiet}) {
        local *STDOUT;
        open STDOUT, '>', devnull() or die "failed to redirect stdout: $!";
        my $status = system { $cmd[0] } @cmd;
        _check_status($status, \@cmd);
        return;
      }
      my $status = system { $cmd[0] } @cmd;
      _check_status($status, \@cmd);
      return;
    },
  );
}

sub run_cmd_capture {
  my ($opts, @cmd) = ref($_[0]) eq 'HASH' ? @_ : ({}, @_);
  die "missing command" if !@cmd;
  return _run_with_context(
    $opts,
    sub {
      my $stderr = gensym();
      my $pid = open3(undef, my $stdout, $stderr, @cmd);
      local $/;
      my $out = <$stdout>;
      my $err = <$stderr>;
      close $stdout;
      close $stderr;
      waitpid($pid, 0);
      my $code = $? >> 8;
      $out = defined $out ? $out : '';
      $err = defined $err ? $err : '';
      return ($code, $out, $err);
    },
  );
}

sub run_script {
  my ($root, $name, @args) = @_;
  run_cmd(script_path($root, $name), @args);
}

sub assert_regex {
  my ($text, $regex, $message) = @_;
  return if $text =~ $regex;
  die $message;
}

sub _check_status {
  my ($status, $cmd) = @_;
  if ($status == -1) {
    die "failed to execute @$cmd: $!";
  }
  my $code = $status >> 8;
  die "command failed ($code): @$cmd\n" if $code != 0;
}

1;
