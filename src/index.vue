<template>
    <div>
        <div class="container-fluid">
            <div class="row" style="padding-top: 20px; padding-bottom: 20px; background-color: #eee;">
                <button id="done" class="btn btn-info ml-2" @click="done" title="Done" :disabled="doneDisabled">Done</button>
                <form class="form-inline mx-auto" action="javascript:false">
                    <div class="form-group">
                        <label for="formula-input">Prove: </label>
                        <input type="text" class="form-control ml-2" id="formula-input" size="40" value="Socrates:(), Human::(), Mortal::(); Human(Socrates), forall x:(). Human(x) -> Mortal(x) |- Mortal(Socrates)" />
                    </div>
                    <button type="submit" class="btn btn-outline-secondary" id="parse" @click="parseGoal" :disabled="parseDisabled">Start</button>
                </form>
                <div class="buttons text-right mr-2">
                    <button class="btn btn-outline-secondary btn-select" @click="toggleSelectionMode" title="Undo (ctrl+z)"><i class="fas fa-mouse-pointer fa-sm"></i></button>
                    <button class="btn btn-outline-secondary btn-undo" @click="undo" title="Undo (ctrl+z)"><i class="fas fa-undo"></i></button>
                    <button class="btn btn-outline-secondary btn-redo" @click="redo" title="Undo (ctrl+y)"><i class="fas fa-redo"></i></button>
                </div>
            </div>
            <div class="row" style="height: calc(100vh - 78px)">
                <div class="container-fluid pi-canvas" id="prover-canvas" style="padding-left: 0; padding-right: 0;">
                    <proof-canvas ref="proofCanvas"></proof-canvas>
                </div>
            </div>
        </div>
    </div>
</template>

<script>
import ProofCanvas from "./components/proofCanvas.vue";
import Vue from "vue";

const vue2TouchEvents = require("vue2-touch-events");
Vue.use(vue2TouchEvents);

export default {
    components: {
        ProofCanvas,
    },
    created() {
        window.ipcRenderer.on("action", (_, goalb) => {
            try {
                window.goal = window.goal.setgoalb(goalb);
                this.$refs.proofCanvas.setGoal(window.goal);
                this.setProofMode("server");
            } catch (e) {
                this.$refs.proofCanvas.showErrorMessage(e);
                window.ipcRenderer.send('error', this.$refs.proofCanvas.errorMsg);
            }
        })
    },
    updated() {
    },
    mounted() {
        window.vue = this; // for debug purposes

        // load lemma db
        this.loadLemmaDB();

        // when prover is ready, enable parse button
        this.parseDisabled = false;

        // manage the url parameter goal if there is one
        var goal = this.loadGoal();
        if (goal) {
            $("#formula-input").val(goal);
        }
        this.parseGoal();

        // also capture ctrl+z and ctrl+y and M for MathML
        var self = this;
        $(document).keydown(function (e) {
            if (!$('input[type="text"]').is(":focus")) {
                // dont capture on textboxes
                if (e.key === "y" && e.ctrlKey) {
                    // ctrl+y
                    self.redo();
                } else if (e.key === "z" && e.ctrlKey) {
                    // ctrl+z
                    self.undo();
                } else if (e.key === "m" && e.ctrlKey) {
                    self.toggleDisplayMode();
                }
            }

            if (e.key == "Shift" && !e.ctrlKey) {
                // shift
                self.enterSelectionMode();
            }
        });

        $(document).keyup(function (e) {
            if (e.key == "Shift" || e.keyCode === 27) {
                // release shift or escape
                self.exitSelectionMode();
            }
        });
    },
    data() {
        return {
            goal: null,
            parseDisabled: true,
            doneDisabled: true,
        };
    },

    methods: {
        loadLemmaDB() {
            let $this = this;
            $.getJSON("lemmas.json", function(lemmas) {
                var goal = window.goal.loaddb(lemmas);
                $this.$refs.proofCanvas.setGoal(goal);
            });
        },

        loadGoal() {
            var result = null,
                tmp = [];
            var items = window.location.search.substr(1).split("&");
            for (var index = 0; index < items.length; index++) {
                tmp = items[index].split("=");
                if (tmp[0] === "goal") result = decodeURIComponent(tmp[1]);
            }
            return result ? atob(result) : null;
        },

        saveGoal(goal) {
            var proofString = window.goal.subgoals()[0].conclusion().tostring();
            document.title = "Prove: " + proofString;
        },

        parseGoal(e) {
            if (e) {
                e.preventDefault();
                e.stopPropagation();
            }
            this.setDisplayMode("html");
            var input = $("#formula-input").val().trim();
            try {
                let goal = (window.goal = engine.parse(input)); // window.goal for debug
                this.$refs.proofCanvas.setGoal(goal);
                this.saveGoal(input);
            } catch (e) {
                this.$refs.proofCanvas.showErrorMessage(e);
            }
        },

        toggleSelectionMode() {
            if (this.$refs.proofCanvas.selectMode) {
                this.exitSelectionMode();
            } else {
                this.enterSelectionMode();
            }
        },

        enterSelectionMode() {
            this.$refs.proofCanvas.enterSelectMode();
        },

        exitSelectionMode() {
            this.$refs.proofCanvas.exitSelectMode();
        },

        toggleDisplayMode() {
            if (this.$refs.proofCanvas.displayMode === "html") {
                this.setDisplayMode("mathml");
            } else {
                this.setDisplayMode("html");
            }
        },

        setDisplayMode(mode) {
            this.$refs.proofCanvas.setDisplayMode(mode);
        },

        undo() {
            this.$refs.proofCanvas.undo();
        },

        redo() {
            this.$refs.proofCanvas.redo();
        },

        setProofMode(mode) {
            switch (mode) {
                case "server":
                    this.parseDisabled = true;
                    this.doneDisabled = false;
                    break;
                case "draft":
                    this.parseDisabled = false;
                    this.doneDisabled = true;
                    break;
                default:
                    break;
            }
        },

        updateClient() {
            try {
                let proofb = window.goal.getproofb();
                window.ipcRenderer.send('action', proofb);
            } catch (e) {
                this.$refs.proofCanvas.showErrorMessage(e);
                window.ipcRenderer.send('error', this.$refs.proofCanvas.errorMsg);
            }
        },

        done() {
            this.updateClient();
            this.setProofMode("draft");
        },

        toggleMenu() {},
    },
};
</script>

<style>
.html,
body {
    margin: 0;
    padding: 0;
    height: 100vh;
    overflow: hidden;
}

span.MJXc-display,
span.MJXc-display * {
    -webkit-touch-callout: none;
    -webkit-user-select: none;
    -khtml-user-select: none;
    -moz-user-select: none;
    -ms-user-select: none;
    user-select: none;
}

div.formula_box {
    position: absolute;
    font: 30pt arial;
    border: 1px solid;
    margin: 0pt;
    padding: 0.3em;
    display: inline;
}

div.formula {
    font: 30pt arial;
    display: inline;
}

div.qed {
    font: 100pt arial;
    display: inline;
}

.btn:focus {
    box-shadow: none !important;
    outline: none !important;
}
</style>
