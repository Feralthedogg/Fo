package Fo::Scripts;

use strict;
use warnings;

use Cwd qw(abs_path);
use Digest::SHA qw(sha256_hex);
use Exporter qw(import);
use File::Basename qw(basename dirname);
use File::Find qw(find);
use File::Spec;
use File::Temp qw(tempdir tempfile);
use Fo::Util;

our @EXPORT = qw(dispatch_script);
my %FILE_HASH_CACHE;

sub dispatch_script {
  my ($script_name, $script_dir, @args) = @_;
  my $root = repo_root_from($script_dir);
  my %dispatch = (
    'build-cli-core.sh'                  => \&build_cli_core,
    'build-cold-seed-cli.sh'            => \&build_cold_seed_cli,
    'build-release-artifacts.sh'        => \&build_release_artifacts,
    'build-selfhosted-cli.sh'           => \&build_selfhosted_cli,
    'build-windows-msi.sh'              => \&build_windows_msi,
    'clean-cache.sh'                    => \&clean_cache,
    'check-bootstrapless-rebuild.sh'    => \&check_bootstrapless_rebuild,
    'check-canonical-go-core.sh'        => \&check_canonical_go_core,
    'check-cold-seed-cli.sh'            => \&check_cold_seed_cli,
    'check-formal-coq.sh'               => \&check_formal_coq,
    'check-formal-lean.sh'              => \&check_formal_lean,
    'check-formal.sh'                   => \&check_formal,
    'check-generated-base-runtime.sh'   => \&check_generated_base_runtime,
    'check-genesis-bootstrap-candidate.sh' => \&check_genesis_bootstrap_candidate,
    'check-genesis-interpreter-smoke.sh'   => \&check_genesis_interpreter_smoke,
    'check-genesis-seed-executor.sh'       => \&check_genesis_seed_executor,
    'check-genesis-seed-materialization.sh' => \&check_genesis_seed_materialization,
    'check-genesis-seedplan-parity.sh'     => \&check_genesis_seedplan_parity,
    'check-no-genesis-build-dependency.sh' => \&check_no_genesis_build_dependency,
    'check-selfhosted-workflow.sh'         => \&check_selfhosted_workflow,
    'freeze-seed-snapshot.sh'              => \&freeze_seed_snapshot,
    'generate-base-bridge-runtime.sh'      => \&generate_base_bridge_runtime,
    'generate-base-collections-runtime.sh' => \&generate_base_collections_runtime,
    'generate-base-effects-runtime.sh'     => \&generate_base_effects_runtime,
    'generate-base-stdlib-runtime.sh'      => \&generate_base_stdlib_runtime,
    'materialize-genesis-seed.sh'          => \&materialize_genesis_seed,
    'publish-genesis-seed.sh'              => \&publish_genesis_seed,
    'publish-seed-snapshot.sh'             => \&publish_seed_snapshot,
    'promote-selfhosted-cli.sh'            => \&promote_selfhosted_cli,
  );
  my $handler = $dispatch{$script_name}
    or die "unknown script entrypoint: $script_name\n";
  $handler->($root, @args);
}

sub quiet_stdout {
  my ($code) = @_;
  open my $null, '>', devnull() or die "failed to open devnull: $!";
  local *STDOUT = $null;
  $code->();
}

sub cleanup_root_generated_full {
  my ($root) = @_;
  remove_paths(
    "$root/internal/token/token.go",
    "$root/internal/diagnostic/diagnostic.go",
    "$root/internal/ast/ast.go",
    "$root/internal/lexer/lexer.go",
    "$root/internal/parser/parser.go",
    "$root/internal/checker/checker.go",
    "$root/internal/codegen/codegen.go",
    "$root/internal/driver/driver.go",
    "$root/internal/fomod/fomod.go",
    "$root/internal/project/project.go",
    "$root/internal/formatfo/format.go",
    "$root/internal/toolchain/toolchain.go",
    "$root/internal/hostplan/hostplan.go",
    "$root/cmd/fo/main.go",
    "$root/cmd/fohost/main.go",
    "$root/stdlib/fo/base.go",
    "$root/stdlib/fo/collections.go",
    "$root/stdlib/fo/effects.go",
  );
}

sub cleanup_root_generated_partial {
  my ($root) = @_;
  remove_paths(
    "$root/internal/token/token.go",
    "$root/internal/diagnostic/diagnostic.go",
    "$root/internal/ast/ast.go",
    "$root/internal/lexer/lexer.go",
    "$root/internal/parser/parser.go",
    "$root/internal/checker/checker.go",
    "$root/internal/codegen/codegen.go",
    "$root/internal/driver/driver.go",
    "$root/internal/fomod/fomod.go",
    "$root/internal/project/project.go",
    "$root/internal/formatfo/format.go",
    "$root/internal/toolchain/toolchain.go",
    "$root/cmd/fo/main.go",
    "$root/stdlib/fo/base.go",
    "$root/stdlib/fo/collections.go",
    "$root/stdlib/fo/effects.go",
  );
}

sub ensure_fo_bin {
  my ($root) = @_;
  my $bin = -x "$root/build/fo" ? "$root/build/fo" : "$root/build/fo-selfhosted";
  if (!-x $bin) {
    die "missing self-hosted seed\nrun scripts/promote-selfhosted-cli.sh first\n";
  }
  return $bin;
}

sub resolve_generation_bin {
  my ($root) = @_;
  my $env_bin = $ENV{FO_BIN};
  return $env_bin if defined $env_bin && -x $env_bin;
  my $bin = -x "$root/build/fo" ? "$root/build/fo" : "$root/build/fo-selfhosted";
  return $bin if -x $bin;
  die "missing Fo compiler binary\n";
}

sub resolve_genesis_bins {
  my ($root) = @_;
  my $core_bin = resolve_generation_bin($root);
  die "missing compiler seed\n" if !-x $core_bin;
  return ($core_bin, $core_bin);
}

sub strings_contains {
  my ($text, $needle) = @_;
  return index($text, $needle) >= 0;
}

sub cached_file_hash {
  my ($path) = @_;
  return $FILE_HASH_CACHE{$path} if exists $FILE_HASH_CACHE{$path};
  my $content = read_file($path);
  my $hash = sha256_hex($content);
  $FILE_HASH_CACHE{$path} = $hash;
  return $hash;
}

sub build_cli_core_cache_root {
  my ($root) = @_;
  return cache_root($root) . "/build-cli-core";
}

sub build_cli_core_key {
  my ($root, $kind, $path, $bin) = @_;
  return sha256_hex(join(
    "\0",
    "build-cli-core-v1",
    $kind,
    $path,
    cached_file_hash("$root/$path"),
    cached_file_hash($bin),
  ));
}

sub stdlib_cache_root {
  my ($root) = @_;
  return cache_root($root) . "/stdlib-go";
}

sub cache_root {
  my ($root) = @_;
  my $cache_root = $ENV{FO_CACHE_ROOT};
  return $cache_root if defined $cache_root && $cache_root ne '';
  return "$root/.fo-cache";
}

sub repo_relative_path {
  my ($root, $path) = @_;
  my $abs_root = abs_path($root);
  my $abs_path = abs_path($path);
  return undef if !defined $abs_root || !defined $abs_path;
  return '.' if $abs_root eq $abs_path;
  return undef if index($abs_path, $abs_root . '/') != 0;
  my $rel = File::Spec->abs2rel($abs_path, $abs_root);
  $rel =~ s{\\}{/}g;
  return $rel;
}

sub repo_relative_cache_root {
  my ($root) = @_;
  return repo_relative_path($root, cache_root($root));
}

sub build_workspace_root {
  my ($root) = @_;
  return $ENV{FO_WORKSPACE_ROOT} // "$root/.fo-build";
}

sub build_stage_root {
  my ($root) = @_;
  return $ENV{FO_STAGE_ROOT} // "$root/.fo-build-stage";
}

sub with_temp_build_roots {
  my ($root, $code) = @_;
  my $sandbox = tempdir('.fo-build-run.XXXXXX', DIR => $root, CLEANUP => 1);
  local $ENV{FO_WORKSPACE_ROOT} = "$sandbox/work";
  local $ENV{FO_STAGE_ROOT} = "$sandbox/stage";
  return $code->();
}

sub canonical_seed_dir {
  my ($root) = @_;
  return "$root/bootstrap/seed";
}

sub canonical_genesis_seed_dir {
  my ($root) = @_;
  return "$root/bootstrap/seed-genesis";
}

sub temp_seed_dir {
  my ($root) = @_;
  return tempdir('.seed-freeze.XXXXXX', DIR => $root, CLEANUP => 0);
}

sub temp_genesis_seed_dir {
  my ($root) = @_;
  return tempdir('.seed-genesis.XXXXXX', DIR => $root, CLEANUP => 0);
}

sub build_cli_core {
  my ($root, @args) = @_;
  my $fo_bin = shift @args or die "usage: build-cli-core.sh <fo-binary>\n";
  my $workspace_root = build_workspace_root($root);
  my $stage_root = build_stage_root($root);
  my $fohost_bin = $ENV{FOHOST_BIN};
  my $keep = ($ENV{KEEP_ROOT_GENERATED} // '0') eq '1';
  my $cache_root = build_cli_core_cache_root($root);
  my %emit_go_supported;
  my @build_layers = (
    ["internal/token/token.fo", "internal/diagnostic/diagnostic.fo", "internal/project/project.fo"],
    ["internal/ast/ast.fo", "internal/fomod/fomod.fo", "internal/hostplan/hostplan.fo"],
    ["internal/lexer/lexer.fo", "internal/checker/checker.fo", "internal/codegen/codegen.fo"],
    ["internal/parser/parser.fo"],
    ["internal/driver/driver.fo"],
    ["internal/toolchain/toolchain.fo"],
    ["cmd/fo/main.fo"],
    ["cmd/fohost/main.fo"],
  );
  my @checks = (
    "stdlib/fo/base.fo",
    "stdlib/fo/collections.fo",
    "stdlib/fo/effects.fo",
  );
  my $error;
  eval {
    remove_paths($workspace_root, $stage_root);
    ensure_dir($workspace_root, $stage_root);
    ensure_dir("$cache_root/build", "$cache_root/check");

    my $supports_emit_go = sub {
      my ($bin) = @_;
      return $emit_go_supported{$bin} if exists $emit_go_supported{$bin};
      my (undef, $out, $err) = run_cmd_capture($bin, 'emit-go');
      my $text = $out . $err;
      my $ok = !strings_contains($text, "unknown command: emit-go");
      $emit_go_supported{$bin} = $ok;
      return $ok;
    };

    my $legacy_sync_generated_file = sub {
      my ($path) = @_;
      (my $go_path = $path) =~ s/\.fo$/.go/;
      my $src = "$root/$go_path";
      my $dst = "$stage_root/$go_path";
      my $workspace_src = "$workspace_root/$go_path";
      if (!-f $src) {
        if (-f $workspace_src) {
          copy_file($workspace_src, $dst);
          return;
        }
        die "missing generated file for $path\n";
      }
      copy_file($src, $dst);
    };

    my $build_file = sub {
      my ($path) = @_;
      my $bin = ($path eq 'cmd/fohost/main.fo' && defined $fohost_bin && -x $fohost_bin) ? $fohost_bin : $fo_bin;
      my $key = build_cli_core_key($root, 'build', $path, $bin);
      (my $go_path = $path) =~ s/\.fo$/.go/;
      my $cached_go = "$cache_root/build/$key.go";
      if (-f $cached_go) {
        copy_file($cached_go, "$stage_root/$go_path");
        return;
      }
      if ($supports_emit_go->($bin)) {
        my ($code, $stdout, $stderr) = run_cmd_capture($bin, 'emit-go', $path);
        if ($code != 0) {
          my $msg = $stderr ne '' ? $stderr : $stdout;
          die ($msg ne '' ? $msg : "emit-go failed for $path\n");
        }
        write_file("$stage_root/$go_path", $stdout);
        run_cmd('gofmt', '-w', "$stage_root/$go_path");
        copy_file("$stage_root/$go_path", $cached_go);
        return;
      }
      run_cmd($bin, 'build', $path);
      $legacy_sync_generated_file->($path);
      copy_file("$stage_root/$go_path", $cached_go);
    };

    my $build_cache_hit = sub {
      my ($path) = @_;
      my $bin = ($path eq 'cmd/fohost/main.fo' && defined $fohost_bin && -x $fohost_bin) ? $fohost_bin : $fo_bin;
      my $key = build_cli_core_key($root, 'build', $path, $bin);
      return -f "$cache_root/build/$key.go";
    };

    my $check_file = sub {
      my ($path) = @_;
      my $key = build_cli_core_key($root, 'check', $path, $fo_bin);
      my $marker = "$cache_root/check/$key.ok";
      return if -f $marker;
      run_cmd({ quiet => 1 }, $fo_bin, 'check', $path);
      write_file($marker, "ok\n");
    };

    for my $layer (@build_layers) {
      my @warm = grep { $build_cache_hit->($_) } @$layer;
      my @cold = grep { !$build_cache_hit->($_) } @$layer;
      run_parallel_tasks(map {
        my $path = $_;
        sub { $build_file->($path) }
      } @warm);
      for my $path (@cold) {
        $build_file->($path);
      }
    }
    run_parallel_tasks(map {
      my $path = $_;
      sub { $check_file->($path) }
    } @checks);

    remove_paths("$root/cmd/fohost/main.go");
    ensure_dir("$stage_root/stdlib/fo");
    generate_base_package_to($root, "$stage_root/stdlib/fo", $fo_bin);

    remove_paths($workspace_root);
    ensure_dir($workspace_root);
    write_file(
      "$workspace_root/go.mod",
      "module github.com/Feralthedogg/Fo\n\ngo 1.25.6\n",
    );
    copy_tree_contents($stage_root, $workspace_root);
    1;
  } or do {
    $error = $@ || "build-cli-core failed\n";
  };
  cleanup_root_generated_full($root) if !$keep;
  die $error if defined $error;
}

sub run_parallel_tasks {
  my (@tasks) = @_;
  return if !@tasks;
  my @pids;
  for my $task (@tasks) {
    my $pid = fork();
    die "failed to fork\n" if !defined $pid;
    if ($pid == 0) {
      open my $null, '>', devnull() or die "failed to open devnull: $!";
      local *STDOUT = $null;
      my $ok = eval { $task->(); 1 };
      if (!$ok) {
        print STDERR ($@ || "parallel task failed\n");
        exit 1;
      }
      exit 0;
    }
    push @pids, $pid;
  }
  my $failed = 0;
  for my $pid (@pids) {
    waitpid($pid, 0);
    my $code = $? >> 8;
    if ($code != 0) {
      $failed = 1;
    }
  }
  die "parallel task failed\n" if $failed;
}

sub build_cold_seed_cli {
  my ($root, @args) = @_;
  my $seed_dir = $args[0];
  my $out_bin = $args[1] // "$root/build/fo-coldseed";
  if (!defined $seed_dir) {
    $seed_dir = temp_seed_dir($root);
    print "[0/2] Freezing temporary seed snapshot\n";
    freeze_seed_snapshot($root, $seed_dir);
  }
  if (!-f "$seed_dir/go.mod") {
    die "missing seed snapshot at $seed_dir\npublish one with scripts/publish-seed-snapshot.sh or pass an explicit seed dir\n";
  }
  print "[1/2] Building cold-start CLI from $seed_dir\n";
  ensure_parent($out_bin);
  run_cmd(
    {
      dir => $seed_dir,
      env => { GO111MODULE => 'on', GOWORK => 'off' },
    },
    'go',
    'build',
    '-tags',
    'fo_stage1',
    '-o',
    $out_bin,
    './cmd/fohost',
  );
  print "[2/2] Built cold-start CLI: $out_bin\n";
}

sub build_selfhosted_cli {
  my ($root) = @_;
  my $fo_bin = $ENV{FO_BIN} // "$root/build/fo";
  if (!-x $fo_bin) {
    die "missing self-hosted compiler at $fo_bin\n";
  }
  with_temp_build_roots($root, sub {
    print "[1/2] Re-transpiling Fo CLI core with self-hosted compiler\n";
    build_cli_core($root, $fo_bin);
    print "[2/2] Building self-hosted CLI to build/fo-selfhosted\n";
    ensure_dir("$root/build");
    run_cmd(
      {
        dir => build_workspace_root($root),
        env => { GO111MODULE => 'on', GOWORK => 'off' },
      },
      'go',
      'build',
      '-tags',
      'fo_stage1',
      '-o',
      "$root/build/fo-selfhosted",
      './cmd/fohost',
    );
    print "Built self-hosted CLI: $root/build/fo-selfhosted\n";
    return;
  });
}

sub check_bootstrapless_rebuild {
  my ($root) = @_;
  my $fo_bin = ensure_fo_bin($root);
  my $workdir = "$root/seedwork/current";
  my $error;
  with_temp_build_roots($root, sub {
    ensure_dir("$root/seedwork");
    remove_paths($workdir);
    ensure_dir($workdir);

    print "[1/4] Transpiling CLI core with self-hosted seed only\n";
    local $ENV{KEEP_ROOT_GENERATED} = '1';
    build_cli_core($root, $fo_bin);

    print "[2/4] Building host bridge from generated Fo sources\n";
    ensure_dir(
      "$workdir/bin",
      "$workdir/internal",
      "$workdir/cmd",
      "$workdir/stdlib/fo",
    );
    write_file(
      "$workdir/go.mod",
      "module github.com/Feralthedogg/Fo\n\ngo 1.25.6\n",
    );
    copy_tree_contents(build_workspace_root($root) . "/internal", "$workdir/internal");
    copy_tree_contents(build_workspace_root($root) . "/cmd", "$workdir/cmd");
    copy_tree_contents(build_workspace_root($root) . "/stdlib/fo", "$workdir/stdlib/fo");
    run_cmd(
      {
        dir => $workdir,
        env => { GO111MODULE => 'on', GOWORK => 'off' },
      },
      'go',
      'build',
      '-tags',
      'fo_stage1',
      '-o',
      "$workdir/bin/fo-seeded",
      './cmd/fohost',
    );

    print "[3/4] Smoke-checking seed-built host bridge\n";
    my (undef, $version_out, $version_err) = run_cmd_capture("$workdir/bin/fo-seeded", 'version');
    assert_regex($version_out . $version_err, qr/fo-selfhost-dev/, "missing fo-selfhost-dev in version output\n");
    my (undef, $help_out, $help_err) = run_cmd_capture("$workdir/bin/fo-seeded", 'help');
    assert_regex($help_out . $help_err, qr/fo build/, "missing fo build in help output\n");

    write_file(
      "$workdir/sample.fo",
      "package main\n\nfunc main() {\n    return\n}\n",
    );
    print "[4/4] Check/build/run with seed-built host bridge\n";
    my (undef, $check_out, $check_err) = run_cmd_capture("$workdir/bin/fo-seeded", 'check', "$workdir/sample.fo");
    assert_regex($check_out . $check_err, qr/check passed/, "seeded check did not report success\n");
    run_cmd("$workdir/bin/fo-seeded", 'build', "$workdir/sample.fo");
    die "missing built file $workdir/sample.go\n" if !-f "$workdir/sample.go";
    run_cmd({ quiet => 1 }, "$workdir/bin/fo-seeded", 'run', "$workdir/sample.fo");

    print "Bootstrapless rebuild path verified.\n";
    return 1;
  }) or do {
    $error = $@ || "bootstrapless rebuild failed\n";
  };
  cleanup_root_generated_partial($root);
  remove_paths($workdir);
  rmdir("$root/seedwork") if -d "$root/seedwork";
  die $error if defined $error;
}

sub check_canonical_go_core {
  my ($root) = @_;
  print "[1/3] Checking canonical handwritten Go core set\n";
  my $cache_rel = repo_relative_cache_root($root);
  my @files;
  collect_go_files(
    $root,
    sub {
      my ($rel) = @_;
      return 0 if defined $cache_rel && ($rel eq $cache_rel || index($rel, $cache_rel . '/') == 0);
      return 0 if $rel =~ m{^\.(?:fo-build|fo-build-stage)/};
      return 0 if $rel =~ m{^seedwork/};
      return 1 if $rel =~ /\.go\z/;
      return 0;
    },
    \@files,
  );
  my @handwritten = grep { !file_has_generated_header("$root/$_") } @files;
  if (@handwritten) {
    die "unexpected handwritten Go core set\n" . join("\n", @handwritten) . "\n";
  }

  print "[2/3] Checking removed legacy paths stay absent\n";
  for my $path ('bootstrap/support', 'bootstrap/bin', 'pkg/hostexec') {
    die "legacy path still exists: $path\n" if -e "$root/$path";
  }

  print "[3/3] Canonical Go core verified\n";
}

sub clean_cache {
  my ($root, @args) = @_;
  my $target = $args[0] // cache_root($root);
  print "Removing cache root: $target\n";
  remove_paths($target);
  print "Cache root removed.\n";
}

sub build_release_artifacts {
  my ($root, @args) = @_;
  my $version = shift @args or die "usage: build-release-artifacts.sh <version> [out-dir]\n";
  my $out_dir_arg = shift @args // "$root/dist/release";
  my $out_dir = File::Spec->file_name_is_absolute($out_dir_arg)
    ? $out_dir_arg
    : File::Spec->catdir($root, $out_dir_arg);
  my $fo_bin = ensure_fo_bin($root);
  my @targets = (
    { os => 'linux',   arch => 'amd64', ext => '',     archive => 'tar.gz' },
    { os => 'linux',   arch => 'arm64', ext => '',     archive => 'tar.gz' },
    { os => 'darwin',  arch => 'amd64', ext => '',     archive => 'tar.gz' },
    { os => 'darwin',  arch => 'arm64', ext => '',     archive => 'tar.gz' },
    { os => 'windows', arch => 'amd64', ext => '.exe', archive => 'zip' },
  );

  remove_paths($out_dir);
  ensure_dir($out_dir, "$out_dir/raw");
  copy_file("$root/packaging/release/install.sh", "$out_dir/install.sh");
  copy_file("$root/packaging/release/install.ps1", "$out_dir/install.ps1");

  my @checksum_files = ("$out_dir/install.sh", "$out_dir/install.ps1");

  with_temp_build_roots($root, sub {
    print "[1/3] Generating release workspace\n";
    build_cli_core($root, $fo_bin);
    my $workspace = build_workspace_root($root);

    print "[2/3] Building release binaries\n";
    for my $target (@targets) {
      my $raw_name = release_raw_binary_name($target);
      my $raw_bin = "$out_dir/raw/$raw_name";
      my %env = (
        GO111MODULE   => 'on',
        GOWORK        => 'off',
        CGO_ENABLED   => '0',
        GOOS          => $target->{os},
        GOARCH        => $target->{arch},
      );
      run_cmd(
        {
          dir => $workspace,
          env => \%env,
        },
        'go',
        'build',
        '-tags',
        'fo_stage1',
        '-o',
        $raw_bin,
        './cmd/fohost',
      );

      my $asset = release_archive_path($out_dir, $version, $target);
      package_release_binary($raw_bin, $asset, $target);
      push @checksum_files, $asset;
    }

    print "[3/3] Writing checksums\n";
    write_release_checksums("$out_dir/checksums.txt", @checksum_files);
    print "$out_dir\n";
    return 1;
  });
}

sub build_windows_msi {
  my ($root, @args) = @_;
  my $version = shift @args or die "usage: build-windows-msi.sh <version> <fo-exe> <out-msi>\n";
  my $exe_path = shift @args or die "usage: build-windows-msi.sh <version> <fo-exe> <out-msi>\n";
  my $out_path = shift @args or die "usage: build-windows-msi.sh <version> <fo-exe> <out-msi>\n";
  die "missing Windows executable at $exe_path\n" if !-f $exe_path;

  my $tmpdir = tempdir('.wix-build.XXXXXX', DIR => $root, CLEANUP => 1);
  my $wxs = "$tmpdir/fo.wxs";
  my $obj = "$tmpdir/fo.wixobj";
  my $msi_version = normalize_msi_version($version);
  my $abs_exe = abs_path($exe_path);

  write_file($wxs, windows_wxs($msi_version));
  ensure_parent($out_path);

  run_cmd(
    'candle.exe',
    '-nologo',
    "-dFoVersion=$msi_version",
    "-dFoExe=$abs_exe",
    '-out',
    $obj,
    $wxs,
  );
  run_cmd(
    'light.exe',
    '-nologo',
    '-out',
    $out_path,
    $obj,
  );
  print "$out_path\n";
}

sub release_raw_binary_name {
  my ($target) = @_;
  return "fo-$target->{os}-$target->{arch}$target->{ext}";
}

sub release_archive_name {
  my ($version, $target) = @_;
  return "fo-$version-$target->{os}-$target->{arch}.$target->{archive}";
}

sub release_archive_path {
  my ($out_dir, $version, $target) = @_;
  return "$out_dir/" . release_archive_name($version, $target);
}

sub package_release_binary {
  my ($raw_bin, $asset, $target) = @_;
  my $pkgdir = tempdir('.release-pkg.XXXXXX', CLEANUP => 1);
  my $binary_name = "fo$target->{ext}";
  copy_file($raw_bin, "$pkgdir/$binary_name");
  if ($target->{archive} eq 'tar.gz') {
    run_cmd({ dir => $pkgdir }, 'tar', '-czf', $asset, $binary_name);
    return;
  }
  if ($target->{archive} eq 'zip') {
    run_cmd({ dir => $pkgdir }, 'zip', '-q', $asset, $binary_name);
    return;
  }
  die "unknown archive format: $target->{archive}\n";
}

sub write_release_checksums {
  my ($path, @files) = @_;
  my @lines;
  for my $file (@files) {
    next if !-f $file;
    push @lines, release_checksum_line($file);
  }
  write_file($path, join("", @lines));
}

sub release_checksum_line {
  my ($path) = @_;
  open my $fh, '<', $path or die "failed to read $path: $!";
  binmode $fh;
  my $sha = Digest::SHA->new(256);
  $sha->addfile($fh);
  close $fh or die "failed to close $path: $!";
  return $sha->hexdigest . "  " . basename($path) . "\n";
}

sub normalize_msi_version {
  my ($version) = @_;
  $version =~ s/^v//;
  $version =~ s/-.*$//;
  my @parts = split /\./, $version;
  @parts = grep { defined $_ && $_ ne '' } @parts;
  while (@parts < 3) {
    push @parts, 0;
  }
  @parts = @parts[0 .. 2];
  @parts = map { $_ =~ /^\d+$/ ? $_ : 0 } @parts;
  return join('.', @parts);
}

sub windows_wxs {
  my ($version) = @_;
  my $xml = <<"WXS";
<?xml version="1.0" encoding="UTF-8"?>
<Wix xmlns="http://schemas.microsoft.com/wix/2006/wi">
  <Product
      Id="*"
      Name="Fo"
      Language="1033"
      Version="__FO_VERSION__"
      Manufacturer="Feralthedogg"
      UpgradeCode="{A5D68D7C-61A1-4F89-BE13-6A70B14E4F31}">
    <Package InstallerVersion="500" Compressed="yes" InstallScope="perUser" />
    <MajorUpgrade DowngradeErrorMessage="A newer version of Fo is already installed." />
    <MediaTemplate EmbedCab="yes" />
    <Property Id="ARPNOMODIFY" Value="1" />

    <Directory Id="TARGETDIR" Name="SourceDir">
      <Directory Id="LocalAppDataFolder">
        <Directory Id="FoProgramsDir" Name="Programs">
          <Directory Id="INSTALLFOLDER" Name="Fo">
            <Component Id="FoExeComponent" Guid="{C0F76C6E-B4B0-4FB0-8F65-41284C62EA21}">
              <File Id="FoExeFile" Name="fo.exe" Source="__FO_EXE__" KeyPath="yes" />
            </Component>
            <Component Id="FoPathComponent" Guid="{0B03E0D2-91F2-44BE-BB3B-F11B364E4FE6}">
              <RegistryValue Root="HKCU" Key="Software\\Fo" Name="InstallDir" Type="string" Value="[INSTALLFOLDER]" KeyPath="yes" />
              <Environment Id="FoAddToPath" Name="PATH" Value="[INSTALLFOLDER]" Part="last" Action="set" System="no" />
            </Component>
          </Directory>
        </Directory>
      </Directory>
    </Directory>

    <Feature Id="MainFeature" Title="Fo" Level="1">
      <ComponentRef Id="FoExeComponent" />
      <ComponentRef Id="FoPathComponent" />
    </Feature>
  </Product>
</Wix>
WXS
  $xml =~ s/__FO_VERSION__/$version/g;
  $xml =~ s/__FO_EXE__/\$\(var.FoExe\)/g;
  return $xml;
}

sub check_cold_seed_cli {
  my ($root) = @_;
  my $tmpdir = tempdir('.cold-seed-check.XXXXXX', DIR => $root, CLEANUP => 1);
  my $seed_dir = "$tmpdir/seed";
  my $cold_bin = "$tmpdir/fo-coldseed";
  print "[1/5] Freezing seed snapshot\n";
  quiet_stdout(sub { freeze_seed_snapshot($root, $seed_dir) });
  print "[2/5] Building cold-start CLI from snapshot\n";
  quiet_stdout(sub { build_cold_seed_cli($root, $seed_dir, $cold_bin) });
  print "[3/5] Version/help smoke\n";
  my (undef, $version_out, $version_err) = run_cmd_capture($cold_bin, 'version');
  assert_regex($version_out . $version_err, qr/fo-selfhost-dev/, "missing fo-selfhost-dev in coldseed version\n");
  my (undef, $help_out, $help_err) = run_cmd_capture($cold_bin, 'help');
  assert_regex($help_out . $help_err, qr/fo build/, "missing fo build in coldseed help\n");

  write_file(
    "$tmpdir/sample.fo",
    "package main\n\nfunc main() {\n    return\n}\n",
  );

  print "[4/5] Check/build/run smoke\n";
  my (undef, $check_out, $check_err) = run_cmd_capture($cold_bin, 'check', "$tmpdir/sample.fo");
  assert_regex($check_out . $check_err, qr/check passed/, "coldseed check did not report success\n");
  run_cmd($cold_bin, 'build', "$tmpdir/sample.fo");
  die "missing built file $tmpdir/sample.go\n" if !-f "$tmpdir/sample.go";
  run_cmd({ quiet => 1 }, $cold_bin, 'run', "$tmpdir/sample.fo");

  print "[5/5] Snapshot path verified\n";
  print "Cold-start seed CLI verified.\n";
}

sub check_formal_coq {
  my ($root) = @_;
  my @files = (
    "proof/coq/Fo/Syntax.v",
    "proof/coq/Fo/Semantics.v",
    "proof/coq/Fo/Env.v",
    "proof/coq/Fo/Pattern.v",
    "proof/coq/Fo/CoreLite.v",
    "proof/coq/Fo/CoreMatch.v",
    "proof/coq/Fo/CoreUpdate.v",
    "proof/coq/Fo/Typing.v",
    "proof/coq/Fo/Codegen.v",
  );
  for my $file (@files) {
    print "== $file ==\n";
    run_cmd({ dir => $root }, 'coqc', '-Q', 'proof/coq/Fo', 'Fo', $file);
  }
}

sub check_formal_lean {
  my ($root) = @_;
  my @files = (
    "proof/lean/Fo/Syntax.lean",
    "proof/lean/Fo/Semantics.lean",
    "proof/lean/Fo/Env.lean",
    "proof/lean/Fo/Pattern.lean",
    "proof/lean/Fo/CoreLite.lean",
    "proof/lean/Fo/CoreMatch.lean",
    "proof/lean/Fo/CoreUpdate.lean",
    "proof/lean/Fo/Typing.lean",
    "proof/lean/Fo/Codegen.lean",
  );
  for my $file (@files) {
    print "== $file ==\n";
    (my $olean = $file) =~ s/\.lean\z/.olean/;
    run_cmd(
      {
        dir => $root,
        env => { LEAN_PATH => 'proof/lean' },
      },
      'lean',
      '-o',
      $olean,
      $file,
    );
  }
}

sub check_formal {
  my ($root) = @_;
  check_formal_lean($root);
  check_formal_coq($root);
}

sub check_generated_base_runtime {
  my ($root) = @_;
  my $tmpdir = tempdir(CLEANUP => 1);
  my $left = "$tmpdir/left";
  my $right = "$tmpdir/right";
  my $fo_bin = resolve_generation_bin($root);

  print "[1/2] Regenerating stdlib/fo runtime package from stdlib/fo/*.fo\n";
  generate_base_package_to($root, $left, $fo_bin);
  generate_base_package_to($root, $right, $fo_bin);

  print "[2/2] Checking generated runtime is stable\n";
  compare_or_die("$left/runtime.go", "$right/runtime.go", "stdlib/fo/runtime.go");
  compare_or_die("$left/collections_generated.go", "$right/collections_generated.go", "stdlib/fo/collections_generated.go");
  compare_or_die("$left/effects_generated.go", "$right/effects_generated.go", "stdlib/fo/effects_generated.go");
  compare_or_die("$left/bridge.go", "$right/bridge.go", "stdlib/fo/bridge.go");
  print "Generated base runtime verified.\n";
}

sub check_genesis_bootstrap_candidate {
  my ($root) = @_;
  print "[1/5] Checking genesis interpreter/toolchain candidate\n";
  check_genesis_interpreter_smoke($root);
  print "[2/5] Checking genesis seed-plan parity against frozen seed\n";
  check_genesis_seedplan_parity($root);
  print "[3/5] Checking genesis seed materialization\n";
  check_genesis_seed_materialization($root);
  print "[4/5] Checking genesis seed executor\n";
  check_genesis_seed_executor($root);
  print "[5/5] Checking cold-seed CLI from frozen snapshot\n";
  check_cold_seed_cli($root);
  print "Genesis bootstrap candidate verified.\n";
}

sub check_genesis_interpreter_smoke {
  my ($root) = @_;
  my ($core_bin, $genesis_bin) = resolve_genesis_bins($root);
  my $error;
  with_temp_build_roots($root, sub {
    my $test_path = build_workspace_root($root) . "/bootstrap/genesis_smoke_test.go";
    print "[1/3] Building genesis interpreter smoke with compiler seed\n";
    build_cli_core($root, $core_bin);
    build_genesis_package($genesis_bin);
    run_cmd({ quiet => 1 }, $genesis_bin, 'build', 'bootstrap/genesis_smoke.fo');
    sync_generated_into_workspace($root, 'internal/genesis/interpreter.go');
    sync_generated_into_workspace($root, 'internal/genesis/toolchain.go');
    sync_generated_into_workspace($root, 'internal/genesis/seedplan.go');
    sync_generated_into_workspace($root, 'bootstrap/genesis_smoke.go');
    write_file(
      $test_path,
      "package main\n\nimport \"testing\"\n\nfunc TestGenesisSmoke(t *testing.T) {\n\tif !Smoke() {\n\t\tt.Fatal(\"genesis interpreter smoke failed\")\n\t}\n}\n",
    );
    print "[2/3] Running genesis interpreter smoke test\n";
    run_cmd(
      {
        dir => build_workspace_root($root),
        env => { GO111MODULE => 'on', GOWORK => 'off' },
      },
      'go',
      'test',
      './bootstrap',
      '-run',
      'TestGenesisSmoke',
      '-count=1',
    );
    print "[3/3] Genesis interpreter smoke verified\n";
    remove_paths($test_path);
    return 1;
  }) or do {
    $error = $@ || "genesis interpreter smoke failed\n";
  };
  remove_paths(
    "$root/internal/genesis/interpreter.go",
    "$root/internal/genesis/toolchain.go",
    "$root/internal/genesis/seedplan.go",
    "$root/bootstrap/genesis_smoke.go",
  );
  die $error if defined $error;
}

sub check_genesis_seed_executor {
  my ($root) = @_;
  my $tmpdir = tempdir('.genesis-seed-check.XXXXXX', DIR => $root, CLEANUP => 1);
  my $seed_dir = "$tmpdir/seed";
  my $target = "$tmpdir/seed-genesis";
  print "[1/4] Refreshing frozen seed snapshot\n";
  quiet_stdout(sub { freeze_seed_snapshot($root, $seed_dir) });
  print "[2/4] Materializing genesis seed\n";
  quiet_stdout(sub { materialize_genesis_seed($root, $target) });
  print "[3/4] Comparing full seed file surface\n";
  my @seed = collect_files($seed_dir);
  my @target = collect_files($target);
  if (join("\n", @seed) ne join("\n", @target)) {
    die "seed file list mismatch\n";
  }
  for my $rel (@seed) {
    my $left = "$seed_dir/$rel";
    my $right = "$target/$rel";
    if (!compare_files($left, $right)) {
      die "seed mismatch: $rel\n";
    }
  }
  print "[4/4] Genesis seed executor verified\n";
}

sub check_genesis_seed_materialization {
  my ($root) = @_;
  my ($core_bin, $genesis_bin) = resolve_genesis_bins($root);
  my $error;
  with_temp_build_roots($root, sub {
    my $seed_dir = tempdir('.seed-materialize.XXXXXX', DIR => $root, CLEANUP => 1);
    my $test_path = build_workspace_root($root) . "/internal/genesis/seedplan_materialization_test.go";
    print "[1/4] Refreshing seed snapshot\n";
    quiet_stdout(sub { freeze_seed_snapshot($root, $seed_dir) });
    print "[2/4] Generating genesis seedplan package in workspace\n";
    build_cli_core($root, $core_bin);
    build_genesis_package($genesis_bin);
    sync_generated_into_workspace($root, 'internal/genesis/interpreter.go');
    sync_generated_into_workspace($root, 'internal/genesis/toolchain.go');
    sync_generated_into_workspace($root, 'internal/genesis/seedplan.go');
    write_file(
      $test_path,
      "package genesis\n\nimport (\n\t\"os\"\n\t\"path/filepath\"\n\t\"strings\"\n\t\"testing\"\n)\n\nfunc TestSeedMaterialization(t *testing.T) {\n\troot := os.Getenv(\"FO_ROOT\")\n\tif root == \"\" {\n\t\tt.Fatal(\"missing FO_ROOT\")\n\t}\n\ttarget := os.Getenv(\"FO_SEED_DIR\")\n\tif target == \"\" {\n\t\ttarget = filepath.Join(root, SeedTargetDir())\n\t}\n\tif got := filepath.Join(target, \"go.mod\"); !fileEquals(got, decodeEscapes(SeedGoModContent())) {\n\t\tt.Fatalf(\"unexpected go.mod content: %s\", got)\n\t}\n\tif got := filepath.Join(target, \"SEED.txt\"); !fileEquals(got, decodeEscapes(SeedManifestContent())) {\n\t\tt.Fatalf(\"unexpected SEED.txt content: %s\", got)\n\t}\n\tfor _, rel := range SeedCanonicalPaths() {\n\t\tif _, err := os.Stat(filepath.Join(target, rel)); err != nil {\n\t\t\tt.Fatalf(\"missing seed path %s: %v\", rel, err)\n\t\t}\n\t}\n}\n\nfunc fileEquals(path string, expected string) bool {\n\tdata, err := os.ReadFile(path)\n\tif err != nil {\n\t\treturn false\n\t}\n\treturn string(data) == expected\n}\n\nfunc decodeEscapes(s string) string {\n\treturn strings.ReplaceAll(s, \"\\\\n\", \"\\n\")\n}\n",
    );
    print "[3/4] Checking seed materialization against Fo-side seedplan\n";
    run_cmd(
      {
        dir => build_workspace_root($root),
        env => { FO_ROOT => $root, FO_SEED_DIR => $seed_dir, GO111MODULE => 'on', GOWORK => 'off' },
      },
      'go',
      'test',
      './internal/genesis',
      '-run',
      'TestSeedMaterialization',
      '-count=1',
    );
    print "[4/4] Genesis seed materialization verified\n";
    remove_paths($test_path);
    return 1;
  }) or do {
    $error = $@ || "genesis seed materialization failed\n";
  };
  remove_paths(
    "$root/internal/genesis/interpreter.go",
    "$root/internal/genesis/toolchain.go",
    "$root/internal/genesis/seedplan.go",
  );
  die $error if defined $error;
}

sub check_genesis_seedplan_parity {
  my ($root) = @_;
  my ($core_bin, $genesis_bin) = resolve_genesis_bins($root);
  my $error;
  with_temp_build_roots($root, sub {
    my $seed_dir = tempdir('.seed-parity.XXXXXX', DIR => $root, CLEANUP => 1);
    my $test_path = build_workspace_root($root) . "/internal/genesis/seedplan_parity_test.go";
    print "[1/4] Refreshing seed snapshot\n";
    quiet_stdout(sub { freeze_seed_snapshot($root, $seed_dir) });
    print "[2/4] Generating genesis package in workspace\n";
    build_cli_core($root, $core_bin);
    build_genesis_package($genesis_bin);
    sync_generated_into_workspace($root, 'internal/genesis/interpreter.go');
    sync_generated_into_workspace($root, 'internal/genesis/toolchain.go');
    sync_generated_into_workspace($root, 'internal/genesis/seedplan.go');
    print "[3/4] Checking full seed-plan parity\n";
    write_file(
      $test_path,
      "package genesis\n\nimport (\n\t\"os\"\n\t\"path/filepath\"\n\t\"reflect\"\n\t\"sort\"\n\t\"testing\"\n)\n\nfunc TestSeedPlanParity(t *testing.T) {\n\troot := os.Getenv(\"FO_ROOT\")\n\tif root == \"\" {\n\t\tt.Fatal(\"missing FO_ROOT\")\n\t}\n\tseedRoot := os.Getenv(\"FO_SEED_DIR\")\n\tif seedRoot == \"\" {\n\t\tseedRoot = filepath.Join(root, SeedTargetDir())\n\t}\n\tactual, err := collectSeedFiles(seedRoot)\n\tif err != nil {\n\t\tt.Fatalf(\"collect seed files: %v\", err)\n\t}\n\texpected := append([]string{}, SeedCanonicalPaths()...)\n\tsort.Strings(expected)\n\tif !reflect.DeepEqual(actual, expected) {\n\t\tt.Fatalf(\"seed file set mismatch\\nactual=%v\\nexpected=%v\", actual, expected)\n\t}\n}\n\nfunc collectSeedFiles(root string) ([]string, error) {\n\tvar files []string\n\terr := filepath.Walk(root, func(path string, info os.FileInfo, err error) error {\n\t\tif err != nil {\n\t\t\treturn err\n\t\t}\n\t\tif info.IsDir() {\n\t\t\treturn nil\n\t\t}\n\t\trel, err := filepath.Rel(root, path)\n\t\tif err != nil {\n\t\t\treturn err\n\t\t}\n\t\tfiles = append(files, filepath.ToSlash(rel))\n\t\treturn nil\n\t})\n\tif err != nil {\n\t\treturn nil, err\n\t}\n\tsort.Strings(files)\n\treturn files, nil\n}\n",
    );
    run_cmd(
      {
        dir => build_workspace_root($root),
        env => { FO_ROOT => $root, FO_SEED_DIR => $seed_dir, GO111MODULE => 'on', GOWORK => 'off' },
      },
      'go',
      'test',
      './internal/genesis',
      '-run',
      'TestSeedPlanParity',
      '-count=1',
    );
    print "[4/4] Genesis seed plan parity verified\n";
    remove_paths($test_path);
    return 1;
  }) or do {
    $error = $@ || "genesis seed plan parity failed\n";
  };
  remove_paths(
    "$root/internal/genesis/interpreter.go",
    "$root/internal/genesis/toolchain.go",
    "$root/internal/genesis/seedplan.go",
  );
  die $error if defined $error;
}

sub check_no_genesis_build_dependency {
  my ($root) = @_;
  print "[1/2] Checking scripts for direct archived genesis build dependency\n";
  my $pattern = qr/(cd .*archived\/bootstrap\/genesis|archived\/bootstrap\/genesis.*go build|go build.*archived\/bootstrap\/genesis|cd .*Legacy\/bootstrap\/genesis|Legacy\/bootstrap\/genesis.*go build|go build.*Legacy\/bootstrap\/genesis)/;
  my @hits;
  for my $path (collect_files("$root/scripts")) {
    next if $path eq 'check-no-genesis-build-dependency.sh';
    my $full = "$root/scripts/$path";
    next if !-f $full;
    my @lines = slurp_lines($full);
    for my $i (0 .. $#lines) {
      next if $lines[$i] !~ $pattern;
      push @hits, "$full:" . ($i + 1) . ":$lines[$i]";
    }
  }
  if (@hits) {
    die join("\n", @hits) . "\ndirect archived genesis build dependency found in scripts\n";
  }
  print "[2/2] No direct archived genesis build dependency in scripts\n";
}

sub check_selfhosted_workflow {
  my ($root) = @_;
  print "[1/4] Building self-hosted CLI\n";
  build_selfhosted_cli($root);
  my $self = "$root/build/fo-selfhosted";
  print "[2/4] Checking Fo stdlib with self-hosted CLI\n";
  run_cmd({ quiet => 1 }, $self, 'check', "$root/stdlib/fo/base.fo", "$root/stdlib/fo/collections.fo", "$root/stdlib/fo/effects.fo");
  print "[3/4] Checking supported examples with self-hosted CLI\n";
  run_cmd({ quiet => 1 }, $self, 'check', "$root/examples/hello.fo", "$root/examples/tailcall.fo", "$root/examples/struct.fo", "$root/examples/pipeline.fo", "$root/examples/integration.fo", "$root/examples/copyupdate.fo", "$root/examples/enum.fo");
  print "[4/4] Building representative artifacts with self-hosted CLI\n";
  run_cmd({ quiet => 1 }, $self, 'build', "$root/examples/hello.fo");
  run_cmd({ quiet => 1 }, $self, 'build', "$root/stdlib/fo/base.fo");
  print "Self-hosted stage-3 workflow verified.\n";
}

sub freeze_seed_snapshot {
  my ($root, @args) = @_;
  my $target_dir = $args[0] // temp_seed_dir($root);
  my $fo_bin = ensure_fo_bin($root);
  my $error;
  with_temp_build_roots($root, sub {
    print "[1/4] Regenerating compiler core with self-hosted seed\n";
    local $ENV{KEEP_ROOT_GENERATED} = '1';
    build_cli_core($root, $fo_bin);

    print "[2/4] Refreshing seed snapshot at $target_dir\n";
    remove_paths($target_dir);
    ensure_dir(
      "$target_dir/cmd/fohost",
      "$target_dir/internal",
      "$target_dir/cmd",
      "$target_dir/stdlib/fo",
    );
    write_file(
      "$target_dir/go.mod",
      "module github.com/Feralthedogg/Fo\n\ngo 1.25.6\n",
    );
    copy_tree_contents(build_workspace_root($root) . "/internal", "$target_dir/internal");
    copy_tree_contents(build_workspace_root($root) . "/cmd", "$target_dir/cmd");
    copy_tree_contents(build_workspace_root($root) . "/stdlib/fo", "$target_dir/stdlib/fo");

    print "[3/4] Writing snapshot manifest\n";
    write_file(
      "$target_dir/SEED.txt",
      "Cold-start seed snapshot for Fo.\n\nThis directory is generated from the current self-hosted compiler binary in\nbuild/fo and is intended to provide a Go-only seed path without depending on\narchived bootstrap source trees at build time.\n",
    );
    print "[4/4] Seed snapshot ready\n";
    print "$target_dir\n";
    return 1;
  }) or do {
    $error = $@ || "freeze seed snapshot failed\n";
  };
  cleanup_root_generated_partial($root);
  die $error if defined $error;
}

sub publish_seed_snapshot {
  my ($root, @args) = @_;
  my $target_dir = $args[0] // canonical_seed_dir($root);
  freeze_seed_snapshot($root, $target_dir);
}

sub generate_base_package_to {
  my ($root, $target_dir, $fo_bin) = @_;
  ensure_dir($target_dir);
  generate_base_runtime_to($root, "$target_dir/runtime.go", $fo_bin);
  generate_base_collections_to($root, "$target_dir/collections_generated.go", $fo_bin);
  generate_base_effects_to($root, "$target_dir/effects_generated.go", $fo_bin);
  generate_base_bridge_to($root, "$target_dir/bridge.go");
}

sub generate_base_runtime_to {
  my ($root, $target, $fo_bin) = @_;
  generate_base_stdlib_to($root, $target, $fo_bin);
}

sub generate_base_bridge_to {
  my ($root, $target) = @_;
  my $source = "$root/stdlib/fo/bridge.gotmpl";
  die "missing bridge template at $source\n" if !-f $source;
  my $cache_dir = stdlib_cache_root($root);
  ensure_dir($cache_dir);
  my $cache_key = sha256_hex(join("\0", "bridge-gotmpl-v1", cached_file_hash($source)));
  my $cached = "$cache_dir/$cache_key.bridge.go";
  if (-f $cached) {
    copy_file($cached, $target);
    return;
  }
  my ($fh, $tmp) = tempfile();
  print {$fh} "// Code generated from stdlib/fo/bridge.gotmpl. DO NOT EDIT.\n\n";
  print {$fh} read_file($source);
  close $fh;
  copy_file($tmp, $target);
  run_cmd('gofmt', '-w', $target);
  copy_file($target, $cached);
}

sub generate_base_bridge_runtime {
  my ($root, @args) = @_;
  my $target_dir = shift @args or die "usage: generate-base-bridge-runtime.sh <target-dir>\n";
  my $target = "$target_dir/bridge.go";
  generate_base_bridge_to($root, $target);
  print "$target\n";
}

sub generate_base_collections_to {
  my ($root, $target, $fo_bin) = @_;
  my $source = "$root/stdlib/fo/collections.go";
  $fo_bin //= resolve_generation_bin($root);
  my $cache_dir = stdlib_cache_root($root);
  ensure_dir($cache_dir);
  my $cache_key = sha256_hex(join("\0", "collections-go-v1", cached_file_hash("$root/stdlib/fo/collections.fo"), cached_file_hash($fo_bin)));
  my $cached = "$cache_dir/$cache_key.collections_generated.go";
  if (-f $cached) {
    copy_file($cached, $target);
    return;
  }
  run_cmd({ quiet => 1 }, $fo_bin, 'build', 'stdlib/fo/collections.fo');
  die "missing generated stdlib collections Go at $source\n" if !-f $source;
  my @lines = slurp_lines($source);
  my @funcs;
  my $i = 0;
  while ($i <= $#lines) {
    my $line = $lines[$i];
    if ($line !~ /^func /) {
      $i++;
      next;
    }
    my @block = ($line);
    my $depth = count_braces($line);
    $i++;
    while ($i <= $#lines) {
      push @block, $lines[$i];
      $depth += count_braces($lines[$i]);
      $i++;
      last if $depth <= 0;
    }
    my $text = join("\n", @block) . "\n";
    next if $text =~ /panic\(`extern bridge`\)/;
    $text =~ s/base\.//g;
    $text =~ s/func Contains\[A any\]\(/func Contains[A comparable](/g;
    $text =~ s/func containsLoop\[A any\]\(/func containsLoop[A comparable](/g;
    push @funcs, $text;
  }
  my ($fh, $tmp) = tempfile();
  print {$fh} "// Code generated from stdlib/fo/collections.fo. DO NOT EDIT.\n\npackage base\n\n";
  print {$fh} $_ for @funcs;
  close $fh;
  copy_file($tmp, $target);
  run_cmd('gofmt', '-w', $target);
  copy_file($target, $cached);
}

sub generate_base_collections_runtime {
  my ($root, @args) = @_;
  my $target_dir = shift @args or die "usage: generate-base-collections-runtime.sh <target-dir>\n";
  my $target = "$target_dir/collections_generated.go";
  generate_base_collections_to($root, $target, resolve_generation_bin($root));
  print "$target\n";
}

sub generate_base_effects_to {
  my ($root, $target, $fo_bin) = @_;
  my $source = "$root/stdlib/fo/effects.go";
  $fo_bin //= resolve_generation_bin($root);
  my $cache_dir = stdlib_cache_root($root);
  ensure_dir($cache_dir);
  my $cache_key = sha256_hex(join("\0", "effects-go-v1", cached_file_hash("$root/stdlib/fo/effects.fo"), cached_file_hash($fo_bin)));
  my $cached = "$cache_dir/$cache_key.effects_generated.go";
  if (-f $cached) {
    copy_file($cached, $target);
    return;
  }
  run_cmd({ quiet => 1 }, $fo_bin, 'build', 'stdlib/fo/effects.fo');
  die "missing generated stdlib effects Go at $source\n" if !-f $source;
  my @lines = slurp_lines($source);
  my @blocks;
  my $i = 0;
  while ($i <= $#lines) {
    my $line = $lines[$i];
    if ($line =~ /^type /) {
      my @block = ($line);
      $i++;
      while ($i <= $#lines && $lines[$i] !~ /^(func |type )/) {
        push @block, $lines[$i];
        $i++;
      }
      push @blocks, normalize_effects_text(join("\n", @block) . "\n");
      next;
    }
    if ($line =~ /^func /) {
      my @block = ($line);
      my $depth = count_braces($line);
      $i++;
      while ($i <= $#lines) {
        push @block, $lines[$i];
        $depth += count_braces($lines[$i]);
        $i++;
        last if $depth <= 0;
      }
      my $text = normalize_effects_text(join("\n", @block) . "\n");
      next if $text =~ /panic\(`extern bridge`\)/;
      push @blocks, $text;
      next;
    }
    $i++;
  }
  my ($fh, $tmp) = tempfile();
  print {$fh} "// Code generated from stdlib/fo/effects.fo. DO NOT EDIT.\n\npackage base\n\n";
  print {$fh} $_ for @blocks;
  close $fh;
  copy_file($tmp, $target);
  run_cmd('gofmt', '-w', $target);
  copy_file($target, $cached);
}

sub generate_base_effects_runtime {
  my ($root, @args) = @_;
  my $target_dir = shift @args or die "usage: generate-base-effects-runtime.sh <target-dir>\n";
  my $target = "$target_dir/effects_generated.go";
  generate_base_effects_to($root, $target, resolve_generation_bin($root));
  print "$target\n";
}

sub generate_base_stdlib_to {
  my ($root, $target, $fo_bin) = @_;
  my $source = "$root/stdlib/fo/base.go";
  $fo_bin //= resolve_generation_bin($root);
  my $cache_dir = stdlib_cache_root($root);
  ensure_dir($cache_dir);
  my $cache_key = sha256_hex(join("\0", "base-go-v1", cached_file_hash("$root/stdlib/fo/base.fo"), cached_file_hash($fo_bin)));
  my $cached = "$cache_dir/$cache_key.runtime.go";
  if (-f $cached) {
    copy_file($cached, $target);
    return;
  }
  run_cmd({ quiet => 1 }, $fo_bin, 'build', 'stdlib/fo/base.fo');
  die "missing generated stdlib base Go at $source\n" if !-f $source;
  my @lines = slurp_lines($source);
  my $start = -1;
  for my $i (0 .. $#lines) {
    if ($lines[$i] =~ /^type Option\[/) {
      $start = $i;
      last;
    }
  }
  die "missing type section in generated stdlib base\n" if $start < 0;
  my $raw = read_file($source);
  my $body = join("\n", @lines[$start .. $#lines]) . "\n";
  $body =~ s/base\.//g;
  $body =~ s/Value0 T/Value T/g;
  $body =~ s/Value0 E/Error E/g;
  $body =~ s/\{ Value0:/\{ Value:/g;
  $body =~ s/\{ Error:/\{ Error:/g;
  $body =~ s/Err(\[[^\]]+\])\{ Value:/Err$1\{ Error:/g;
  $body =~ s/return UnwrapOr\(/return unwrapOr(/g;
  $body =~ s/return MapOption\(/return mapOption(/g;
  $body =~ s/return FlatMapOption\(/return flatMapOption(/g;
  $body =~ s/return IsSome\(/return isSome(/g;
  $body =~ s/return IsNone\(/return isNone(/g;
  $body =~ s/return UnwrapResult\(/return unwrapResult(/g;
  $body =~ s/return MapResult\(/return mapResult(/g;
  $body =~ s/return FlatMapResult\(/return flatMapResult(/g;
  $body =~ s/return IsOk\(/return isOk(/g;
  $body =~ s/return IsErr\(/return isErr(/g;
  $body =~ s/return unwrapOr\(opt, def\)/return unwrapOr[T](opt, def)/g;
  $body =~ s/return mapOption\(opt, f\)/return mapOption[A, B](opt, f)/g;
  $body =~ s/return flatMapOption\(opt, f\)/return flatMapOption[A, B](opt, f)/g;
  $body =~ s/return isSome\(opt\)/return isSome[T](opt)/g;
  $body =~ s/return isNone\(opt\)/return isNone[T](opt)/g;
  $body =~ s/return unwrapResult\(res, def\)/return unwrapResult[T, E](res, def)/g;
  $body =~ s/return mapResult\(res, f\)/return mapResult[A, B, E](res, f)/g;
  $body =~ s/return flatMapResult\(res, f\)/return flatMapResult[A, B, E](res, f)/g;
  $body =~ s/return isOk\(res\)/return isOk[T, E](res)/g;
  $body =~ s/return isErr\(res\)/return isErr[T, E](res)/g;
  my $imports = $raw =~ /"strings"/ ? "import \"strings\"\n\n" : "";
  my ($fh, $tmp) = tempfile();
  print {$fh} "// Code generated from stdlib/fo/base.fo. DO NOT EDIT.\n\npackage base\n\n";
  print {$fh} $imports;
  print {$fh} $body;
  close $fh;
  copy_file($tmp, $target);
  run_cmd('gofmt', '-w', $target);
  copy_file($target, $cached);
}

sub generate_base_stdlib_runtime {
  my ($root, @args) = @_;
  my $target_dir = shift @args or die "usage: generate-base-stdlib-runtime.sh <target-dir>\n";
  my $target = "$target_dir/runtime.go";
  generate_base_stdlib_to($root, $target, resolve_generation_bin($root));
  print "$target\n";
}

sub materialize_genesis_seed {
  my ($root, @args) = @_;
  my ($core_bin, $genesis_bin) = resolve_genesis_bins($root);
  my $target_dir = $args[0] // temp_genesis_seed_dir($root);
  my $workspace_source = tempdir('.genesis-seed-src.XXXXXX', DIR => $root, CLEANUP => 1);
  my @generated_paths = (
    "cmd/fo/main.go",
    "cmd/fohost/main.go",
    "internal/ast/ast.go",
    "internal/checker/checker.go",
    "internal/codegen/codegen.go",
    "internal/diagnostic/diagnostic.go",
    "internal/driver/driver.go",
    "internal/fomod/fomod.go",
    "internal/hostplan/hostplan.go",
    "internal/lexer/lexer.go",
    "internal/token/token.go",
    "internal/parser/parser.go",
    "internal/project/project.go",
    "internal/toolchain/toolchain.go",
    "stdlib/fo/runtime.go",
    "stdlib/fo/collections_generated.go",
    "stdlib/fo/effects_generated.go",
    "stdlib/fo/bridge.go",
  );
  print "[1/4] Generating compiler core workspace\n";
  with_temp_build_roots($root, sub {
    build_cli_core($root, $core_bin);
    copy_tree_contents(build_workspace_root($root), $workspace_source);
    return;
  });

  print "[2/4] Preparing shell-only genesis materialization\n";
  remove_paths($target_dir);
  ensure_dir($target_dir);

  print "[3/4] Materializing Fo-side genesis seed to $target_dir\n";
  write_file(
    "$target_dir/go.mod",
    "module github.com/Feralthedogg/Fo\n\ngo 1.25.6\n",
  );
  write_file(
    "$target_dir/SEED.txt",
    "Cold-start seed snapshot for Fo.\n\nThis directory is generated from the current self-hosted compiler binary in\nbuild/fo and is intended to provide a Go-only seed path without depending on\narchived bootstrap source trees at build time.\n",
  );
  for my $rel (@generated_paths) {
    copy_file("$workspace_source/$rel", "$target_dir/$rel");
  }
  print "[4/4] Genesis seed materialized\n";
  print "$target_dir\n";
}

sub publish_genesis_seed {
  my ($root, @args) = @_;
  my $target_dir = $args[0] // canonical_genesis_seed_dir($root);
  materialize_genesis_seed($root, $target_dir);
}

sub build_genesis_package {
  my ($bin) = @_;
  run_cmd({ quiet => 1 }, $bin, 'build', 'internal/genesis/interpreter.fo');
  run_cmd({ quiet => 1 }, $bin, 'build', 'internal/genesis/toolchain.fo');
  run_cmd({ quiet => 1 }, $bin, 'build', 'internal/genesis/seedplan.fo');
}

sub sync_generated_into_workspace {
  my ($root, $rel) = @_;
  copy_file("$root/$rel", build_workspace_root($root) . "/$rel");
}

sub promote_selfhosted_cli {
  my ($root) = @_;
  print "[1/2] Building self-hosted CLI\n";
  build_selfhosted_cli($root);
  print "[2/2] Promoting self-hosted CLI to build/fo\n";
  ensure_dir("$root/build");
  copy_file("$root/build/fo-selfhosted", "$root/build/fo");
  print "Promoted self-hosted CLI: $root/build/fo\n";
}

sub snapshot_or_empty {
  my ($src, $dst) = @_;
  if (-f $src) {
    copy_file($src, $dst);
  } else {
    write_file($dst, "");
  }
}

sub compare_or_die {
  my ($left, $right, $label) = @_;
  return if compare_files($left, $right);
  print STDERR "$label changed during regeneration\n";
  system('diff', '-u', $left, $right) if -x '/usr/bin/diff';
  die "$label changed during regeneration\n";
}

sub count_braces {
  my ($line) = @_;
  my $opens = () = $line =~ /\{/g;
  my $closes = () = $line =~ /\}/g;
  return $opens - $closes;
}

sub normalize_effects_text {
  my ($text) = @_;
  $text =~ s/struct\{\s*V0 T;V1 error;\s*\}/(T, error)/gs;
  $text =~ s/Run func\(\) \(\s*T,\s*error\s*\)/Run func() (T, error)/gs;
  $text =~ s/base\.//g;
  return $text;
}

sub collect_go_files {
  my ($root, $want, $out) = @_;
  find(
    {
      no_chdir => 1,
      wanted   => sub {
        my $path = $File::Find::name;
        my $rel = File::Spec->abs2rel($path, $root);
        $rel =~ s{\\}{/}g;
        return if !$want->($rel);
        push @$out, $rel;
      },
    },
    $root,
  );
  @$out = sort @$out;
}

sub file_has_generated_header {
  my ($path) = @_;
  open my $fh, '<', $path or die "failed to read $path: $!";
  my $line = <$fh>;
  close $fh or die "failed to close $path: $!";
  return defined $line && $line =~ m{^// Code generated};
}

1;
