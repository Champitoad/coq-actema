<style scoped>
.search-lemma-bar {
    margin: 10px 10px 20px 0;
}
</style>

<template>
    <vue-simple-suggest class="search-lemma-bar" placeholder="Search lemma..." v-model="lemmaSearchText"
        display-attribute="shortName" value-attribute="name" @select="addLemma" :list="lemmaList"
        :filter-by-query="false" :min-length="0" :preventHide="true" :key="lemmaKey" ref="lemmaSearchBar">
        <div slot="suggestion-item" slot-scope="{ suggestion }">
            <div>{{ suggestion.shortName }} : {{ suggestion.stmt }}</div>
        </div>
    </vue-simple-suggest>
</template>

<script>
import _ from "lodash";

import Vue from 'vue';
import VueSweetalert2 from 'vue-sweetalert2';
import 'sweetalert2/dist/sweetalert2.min.css';

import VueSimpleSuggest from 'vue-simple-suggest'
import 'vue-simple-suggest/dist/styles.css' // Optional CSS

Vue.use(VueSweetalert2);

export default {
    props: ["goal", "context", "vars", "selectMode", "displayMode"],
    components: {
        VueSimpleSuggest
    },
    data: function () {
        return {
            lemmaList: [],
            lemmaSearchText: "",
            // A variable used to force a re-render of the lemma list when needed.
            // This is known as the key-changing technique. For more information see :
            // https://michaelnthiessen.com/force-re-render
            lemmaKey: 0,
        };
    },
    methods: {
        // Callback invoked when we click on an entry in the lemma dropdown (list).
        addLemma: async function (lemma) {
            this.$parent.sendLemma(this.goal, lemma.name);
        },


        updateLemmaList: function () {
            let lemmas = Object.entries(this.$parent.proofState.getlemmas());

            this.lemmaList = _.map(lemmas, l => {
                //console.log(l);
                return { name: l[1][0], shortName: l[1][1], stmt: l[1][2] }
            });

            // Force a re-render of the lemma list.
            this.lemmaKey += 1;
        },

        getLemmaSearchText: function () {
            return this.lemmaSearchText;
        },

        focusLemmaSearchBar: function () {
            // For some reason using "setTimeout" is necessary here.
            // For somewhat of an explanation read :
            // https://bobbyhadz.com/blog/focus-not-working-in-javascript
            setTimeout(() => {
                this.$refs.lemmaSearchBar.input.focus();
            }, 0);
        }
    }
};
</script>
