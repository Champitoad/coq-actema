{
  inputs.dream2nix.url = "github:nix-community/dream2nix/legacy";
  outputs = { self, dream2nix }:
    dream2nix.lib.makeFlakeOutputs {
      systems = ["x86_64-linux"];
      config.projectRoot = ./.;

      source = ./.;

      # `projects` can alternatively be an attrset.
      # `projects` can be omitted if `autoProjects = true` is defined.
      projects = ./projects.toml;
      # autoProjects = true;

      # Configure the behavior of dream2nix when translating projects.
      # A setting applies to all discovered projects if `filter` is unset,
      # or just to a subset or projects if `filter` is used.
      settings = [
        # prefer aggregated source fetching (large FODs)
        {
          aggregate = true;
        }
        # for all impure nodejs projects with just a `package.json`,
        # add arguments for the `package-json` translator
        {
          # filter = project: project.translator == "package-json";
          # subsystemInfo.npmArgs = "--legacy-peer-deps";
          # subsystemInfo.nodejs = 16;
        }
      ];
    };
}